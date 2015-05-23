#include "common.h"
#ifdef INFORMATION

Function calls all run through DoCommand().
	
A function call can either be to a system routine or a user routine. 
	
User routines are like C macros, executed in the context of the caller, so the argument 
are never evaluated prior to the call. If you evaluated an argument during the mustering,
you could get bad answers. Consider:
	One has a function: ^foo(^arg1 ^arg2)  ^arg2 ^arg1
	And one has a call ^foo(($val = 1 ) $val )
This SHOULD look like inline code:  $val  $val = 1 
But evaluation at argument time would alter the value of $val and pass THAT as ^arg2. Wrong.

The calling Arguments to a user function are in an array, whose base starts at callArgumentBase and runs
up to (non-inclusive) callArgumentIndex.

System routines are proper functions, whose callArgumentList may or may not be evaluated. 
The callArgumentList are in an array, whose base starts at index CallingArgumentBase and runs
up to (non-inclusive) CallingArgumentIndex. The description of a system routine tells
how many callArgumentList it expects and in what way. Routines that set variables always pass
that designator as the first (unevaluated) argument and all the rest are evaluated callArgumentList.

The following argument passing is supported
	1. Evaluated - each argument is evaluated and stored (except for a storage argument). 
		If the routine takes optional callArgumentList these are already also evaluated and stored, 
		and the argument after the last actual argument is a null string.
	2. STREAM_ARG - the entire argument stream is passed unevaled as a single argument,
		allowing the routine to handle processing them itself.

All calls have a context of "executingBase" which is the start of the rule causing this 
evaluation. All calls are passed a "buffer" which is spot in the currentOutputBase it
should write any answers.

Anytime a single argument is expected, one can pass a whole slew of them by making
them into a stream, encasing them with ().  The parens will be stripped and the
entire mess passed unevaluated. This makes it analogous to STREAM_ARG, but the latter
requires no excess parens to delimit it.

In general, the system does not test result codes on argument evaluations. So
issuing a FAILRULE or such has no effect there.

#endif

#define MAX_TOPIC_KEYS 5000

#define PLANMARK -1
#define RULEMARK -2

#define MAX_LOG_NAMES 4

char lognames[MAX_LOG_NAMES][200];	
FILE* logfiles[4];

bool planning = false;

#define MAX_REUSE_SAFETY 10
static int reuseIndex = 0;
static char* reuseSafety[MAX_REUSE_SAFETY+1];
static int reuseSafetyCount[MAX_REUSE_SAFETY+1];

static char* months[] = {"January","February","March","April","May","June","July","August","September","October","November","December"};
static char* days[] = {"Sunday","Monday","Tuesday","Wednesday","Thursday","Friday","Saturday"};

int globalDepth = 0;
char* stringPlanBase = 0;
char* backtrackPoint = 0;		// plan code backtrace data
unsigned int currentIterator = 0;		// next value of iterator

//   spot callArgumentList are stored for  function calls
#define MAX_ARG_BYTES MAX_WORD_SIZE * 2
char callArgumentList[MAX_ARGUMENT_COUNT+1][MAX_ARG_BYTES];    // arguments to functions
unsigned int callArgumentBases[MAX_CALL_DEPTH];    // arguments to functions
WORDP callStack[MAX_CALL_DEPTH];
unsigned int callIndex = 0;
unsigned int callArgumentIndex;
unsigned int callArgumentBase;
unsigned int fnVarBase;
bool backtrackable = false;

char lastInputSubstitution[INPUT_BUFFER_SIZE];
TestMode wasCommand; // special result passed back from some commands to control chatscript

static char oldunmarked[MAX_SENTENCE_LENGTH];
static unsigned int spellSet;			// place to store word-facts on words spelled per a pattern
char* currentPlanBuffer;

static int rhymeSet;

//////////////////////////////////////////////////////////
/// BASIC FUNCTION CODE
//////////////////////////////////////////////////////////

void InitFunctionSystem() // register all functions
{
	unsigned int k = 0;
	SystemFunctionInfo *fn;
	while ((fn = &systemFunctionSet[++k]) && fn->word)
	{
		if (*fn->word == '^' ) // not a header
		{
			WORDP D = StoreWord((char*) fn->word,0);
			AddInternalFlag(D,FUNCTION_NAME);
			D->x.codeIndex = (unsigned short)k;
		}
	}

	for (unsigned int i = 0; i < MAX_LOG_NAMES; ++i) 
	{
		lognames[i][0] = 0;
		logfiles[i] = NULL;
	}

	oldunmarked[0] = 0;	// global unmarking has nothing
}

void ResetFunctionSystem()
{
	//   reset function call data
	fnVarBase = callArgumentBase = callArgumentIndex = 0;
}

char* SaveBacktrack(int id)
{
	// save: id, oldbacktrack point, currentfact, current dict,   
	char* mark = AllocateString(NULL,4,sizeof(int),false); 
	if (!mark) return NULL;
	int* i = (int*) mark;
	i[0] = id;										// 1st int is a backtrack label - plan (-1) or rule (other)
	i[1] = (int)(stringPlanBase - backtrackPoint);	// 2nd is old backtrack point value
	i[2] = Fact2Index(factFree);					// 4th is fact base 
	i[3] = Word2Index(dictionaryFree);				// 5th is word base (this entry is NOT used)
	return backtrackPoint = mark;
}

static char* FlushMark() // throw away this backtrack point, maybe reclaim its string space
{
	if (!backtrackPoint) return NULL;
	// we are keeping facts and variable changes, so we cannot reassign the string free space back because it may be in use.
	if (backtrackPoint == stringFree) stringFree = backtrackPoint + (4 * sizeof(int));
	int* i = (int*) backtrackPoint;
	return backtrackPoint = stringPlanBase - i[1];
}

static void RestoreMark()
{	// undo all changes
	if (!backtrackPoint) return;
	int* i = ((int*) backtrackPoint); // skip id

	// revert facts
	FACT* oldF = Index2Fact(i[2]);
	while (factFree > oldF) FreeFact(factFree--); // undo facts to start
	// revert dict entries
	WORDP oldD = Index2Word(i[3]);
	
	// trim dead facts at ends of sets
	for (unsigned int store = 0; store < MAX_FIND_SETS; ++store)
	{
		unsigned int count = FACTSET_COUNT(store) + 1;
		while (--count >= 1)
		{
			if (!(factSet[store][count]->flags & FACTDEAD)) break; // stop having found a live fact
		}
		if (count) SET_FACTSET_COUNT(store,count); // new end
	}
	DictionaryRelease(oldD,backtrackPoint);
	backtrackPoint = stringPlanBase - i[1];
}

void RefreshMark()
{	// undo all changes but leave rule mark in place
	if (!backtrackPoint) return;
	int* i = (int*) backtrackPoint; // point past id, backtrack 
	
	// revert facts
	FACT* oldF = Index2Fact(i[2]);
	while (factFree > oldF) FreeFact(factFree--); // undo facts to start
	// revert dict entries
	WORDP oldD = Index2Word(i[3]);

	// trim dead facts at ends of sets
	for (unsigned int store = 0; store < MAX_FIND_SETS; ++store)
	{
		unsigned int count = FACTSET_COUNT(store) + 1;
		while (--count >= 1)
		{
			if (!(factSet[store][count]->flags & FACTDEAD)) break; // stop having found a live fact
		}
		if (count) SET_FACTSET_COUNT(store,count); // new end
	}

	DictionaryRelease(oldD,backtrackPoint);
}

static void UpdatePlanBuffer()
{
	size_t len = strlen(currentPlanBuffer);
	if (len) // we have output, prep next output
	{
		currentPlanBuffer += len;	// cumulative output into buffer
		*++currentPlanBuffer = ' '; // add a space
		currentPlanBuffer[1] = 0;
	}
}

static unsigned int WildPosition(char* arg)
{
	unsigned int x = GetWildcardID(arg);
	unsigned int n = WILDCARD_START(wildcardPosition[x]);
	if (n == 0 || n > wordCount) n = atoi(wildcardCanonicalText[x]);
	if (n == 0 || n > wordCount) n = 1;
	return n;
}

static FunctionResult PlanCode(WORDP plan, char* buffer)
{  // failing to find a responder is not failure.
#ifdef INFORMATION

	A plan sets a recover point for backtracking and clears it one way or another when it exits.
	A rule sets a backpoint only if it finds some place to backtrack. The rule will clear that point one way or another when it finishes.

	Undoable changes to variables are handled by creating special facts. 
#endif

	if (trace & (TRACE_MATCH|TRACE_PATTERN) && CheckTopicTrace()) Log(STDUSERLOG,"\r\n\r\nPlan: %s ",plan->word);
	bool oldplan = planning;
	bool oldbacktrackable = backtrackable;
	char* oldbacktrackPoint = backtrackPoint;
	char* oldStringPlanBase = stringPlanBase;
	stringPlanBase = stringFree;
	backtrackPoint = stringFree;
	backtrackable = false;
	unsigned int oldWithinLoop = withinLoop;
	withinLoop = 0;
	planning = true;
	int holdd = globalDepth;
	ChangeDepth(1,"PlanCode");
	char* oldCurrentPlanBuffer = currentPlanBuffer;
	
	unsigned int tindex = topicIndex;
    FunctionResult result = NOPROBLEM_BIT;

	SAVEOLDCONTEXT()

	// where future plans will increment naming
	char name[MAX_WORD_SIZE];
	strcpy(name,plan->word);
	char* end = name + plan->length;
	*end = '.';
	*++end = 0;

	unsigned int n = 0;
	while (result == NOPROBLEM_BIT) // loop on plans to use
	{
		*buffer = 0;
		currentPlanBuffer = buffer;	  // where we are in buffer writing across rules of a plan
		unsigned int topic = plan->x.topicIndex;
		if (!topic)  
		{
			result = FAILRULE_BIT; 
			break;
		}
		int pushed =  PushTopic(topic);  // sets currentTopicID
		if (pushed < 0) 
		{
			result = FAILRULE_BIT; 
			break;
		}
		char* xxplanMark = SaveBacktrack(PLANMARK); // base of changes the plan has made
		char* base = GetTopicData(topic); 
		int ruleID = 0;
		currentRuleTopic = currentTopicID;
		currentRule = base;
		currentRuleID = ruleID;
		char* ruleMark = NULL;
		while (base && *base ) //   loop on rules of topic
		{
			currentRule = base;
			ruleMark = SaveBacktrack(RULEMARK); // allows rule to be completely undone if it fails
			backtrackable = false;
			result = TestRule(ruleID,base,currentPlanBuffer); // do rule at base
			if (!result || (result & ENDTOPIC_BIT)) // rule didnt fail
			{
				UpdatePlanBuffer();	// keep any results
				if (result & ENDTOPIC_BIT) break; // no more rules are needed
			}
			else if (backtrackable)  // rule failed 
			{
				while (backtrackable)
				{
					if (trace & (TRACE_MATCH|TRACE_PATTERN) && CheckTopicTrace()) Log(STDUSERTABLOG,"Backtrack \r\n");
					*currentPlanBuffer = 0;
					RefreshMark(); // undo all of rule, but leave undo marker in place
					backtrackable = false;
					result = DoOutput(currentPlanBuffer,currentRule,currentRuleID); // redo the rule per normal
					if (!result || result & ENDTOPIC_BIT) break; // rule didnt fail
				}
				if (result & ENDTOPIC_BIT) break; // rule succeeded eventually
			}
			FlushMark();  // cannot revert changes after this
			base = FindNextRule(NEXTTOPLEVEL,base,ruleID);
		}
		if (backtrackPoint == ruleMark) FlushMark(); // discard rule undo
		if (trace & (TRACE_MATCH|TRACE_PATTERN) && CheckTopicTrace()) 
		{
			char* name = GetTopicName(currentTopicID);
			if (*name == '^') Log(STDUSERTABLOG,"Result: %s Plan: %s \r\n",ResultCode(result),name);
			else Log(STDUSERTABLOG,"Result: %s Topic: %s \r\n",ResultCode(result),name);
		}
		if (pushed) PopTopic();
		if (result & ENDTOPIC_BIT) 
		{
			FlushMark(); // drop our access to this space, we are as done as we can get on this rule
			break;	// we SUCCEEDED, the plan is done
		}
		//   flush any deeper stack back to spot we started
		if (result & FAILCODES) topicIndex = tindex; 
		//   or remove topics we matched on so we become the new master path
		RestoreMark(); // undo failed plan
		sprintf(end,"%d",++n);
		plan = FindWord(name);
		result =  (!plan) ? FAILRULE_BIT : NOPROBLEM_BIT;
		if (!result && trace & (TRACE_MATCH|TRACE_PATTERN) && CheckTopicTrace()) Log(STDUSERTABLOG,"NextPlan %s\r\n",name);
	}
	RESTOREOLDCONTEXT()

	ChangeDepth(-1,"PlanCode");
	if (globalDepth != holdd) ReportBug("PlanCode didn't balance");
	
	if (*currentPlanBuffer == ' ') *currentPlanBuffer = 0; // remove trailing space

	// revert to callers environment
	planning = oldplan;
	currentPlanBuffer = oldCurrentPlanBuffer;
	withinLoop = oldWithinLoop;
	backtrackable = oldbacktrackable;
	stringPlanBase = oldStringPlanBase;
	backtrackPoint = oldbacktrackPoint;
	result = (FunctionResult)(result & (-1 ^ (ENDTOPIC_BIT|ENDRULE_BIT)));
	return result; // these are swallowed
}

char* DoFunction(char* name,char* ptr,char* buffer,FunctionResult &result) // DoCall(
{
	WORDP D = FindWord(name,0,LOWERCASE_LOOKUP);
	if (!D || !(D->internalBits & FUNCTION_NAME))
    {
		result = UNDEFINED_FUNCTION;
		return ptr; 
	}
	result = NOPROBLEM_BIT;
	ptr = SkipWhitespace(ptr);
	if (*ptr != '(') // should have been
	{
		result = FAILRULE_BIT;
		return ptr;
	}
	char* paren = ptr;
	ptr = SkipWhitespace(ptr+1); // aim to next major thing after ( 
	bool oldecho = echo; 
	if (D->internalBits & TRACE_MACRO) echo = true;

	SystemFunctionInfo* info = NULL;
	unsigned int oldArgumentBase = callArgumentBase;
	unsigned int oldArgumentIndex = callArgumentIndex;
	unsigned char* definition = NULL;
	if (D->x.codeIndex && !(D->internalBits & (IS_PLAN_MACRO|IS_TABLE_MACRO))) // system function --  macroFlags are also on codeindex, but IS_TABLE_MACRO distinguishes  but PLAN also has a topicindex which is a codeindex
	{
		callArgumentBase = callArgumentIndex - 1;
		if (trace & TRACE_OUTPUT && CheckTopicTrace()) Log(STDUSERTABLOG, "System Call %s(",name);
		info = &systemFunctionSet[D->x.codeIndex];
		char* start = ptr;
		while (ptr && *ptr != ')' && *ptr != ENDUNIT) // read arguments
		{
			if (info->argumentCount != STREAM_ARG) ptr = ReadShortCommandArg(ptr,callArgumentList[callArgumentIndex],result,OUTPUT_NOTREALBUFFER|OUTPUT_EVALCODE|OUTPUT_UNTOUCHEDSTRING);
			else // swallow unevaled arg stream
			{
				ptr = BalanceParen(paren,false);  // start after (, point after closing ) if one can, to next token - it may point 2 after )  or it may point 1 after )
				while (*--ptr != ')'){;} // back up to closing
				size_t len = ptr++ - start; // length of argument bytes not including paren, and end up after paren
				strncpy(callArgumentList[callArgumentIndex],start,len);
				callArgumentList[callArgumentIndex][len] = 0;
			}
			if ((trace & TRACE_OUTPUT || D->internalBits & TRACE_MACRO) && CheckTopicTrace())  Log(STDUSERLOG,"%s, ",callArgumentList[callArgumentIndex]);
			if (++callArgumentIndex >= MAX_ARG_LIST) --callArgumentIndex; // too many arguments globally
			if (info->argumentCount == STREAM_ARG) break; // end of arguments
		}
		*callArgumentList[callArgumentIndex] = 0; //  mark end of arg list with null value
		if ((trace & TRACE_OUTPUT  || D->internalBits & TRACE_MACRO) && CheckTopicTrace()) Log(STDUSERLOG,") = ");
		if (result & ENDCODES); // failed during argument processing
		else if (callArgumentIndex >= (MAX_ARG_LIST-1))	
		{
			ReportBug("System function nesting too deep %d",MAX_ARGUMENT_COUNT);
			result = FAILRULE_BIT;	// too deep calling
		}
		else result = (*info->fn)(buffer);
	} 
	else //   user function (plan macro, inputmacro, outputmacro, tablemacro)) , eg  ^call (_10 ^2 it ^call2 (3 ) )  spot each token has 1 space separator 
	{
		callArgumentBases[callIndex] = callArgumentIndex - 1; // call stack
		callStack[callIndex++] = D;

		unsigned int oldFnVarBase = fnVarBase;
		if ((trace & (TRACE_OUTPUT|TRACE_USERFN) || D->internalBits & TRACE_MACRO) && CheckTopicTrace()) Log(STDUSERTABLOG, "Call %s(",name);
		if (!D->w.fndefinition)
		{
			ReportBug("Missing function definition for %s\r\n",D->word);
			result = FAILRULE_BIT;
		}
		else definition = D->w.fndefinition + 1;
		unsigned int args = MACRO_ARGUMENT_COUNT(D); // expected args

		unsigned int argflags = D->x.macroFlags;
		unsigned int j = 0;
        while (ptr && *ptr && *ptr != ')') //   ptr is after opening (and before an arg but may have white space
        {
			char* arg = callArgumentList[callArgumentIndex++];
			if (callArgumentIndex >= MAX_ARGUMENT_COUNT) --callArgumentIndex; // force lock to fail but swallow all args to update ptr
	
			if (currentRule == NULL) //   this is a table function- DONT EVAL ITS ARGUMENTS AND... keep quoted item intact
			{
				ptr = ReadCompiledWord(ptr,arg); // return dq args as is
#ifndef DISCARDSCRIPTCOMPILER
				if (compiling && ptr == NULL) BADSCRIPT("TABLE-11 Arguments to %s ran out",name)
#endif
			}
			else 
			{
				bool stripQuotes =  (argflags & ( 1 << j)) ? 1 : 0; // want to use quotes 
				// arguments to user functions are not evaluated, they will be used, in place, in the function.
				// EXCEPT evaluation of ^arguments must be immediate to maintain current context- both ^arg and ^"xxx" stuff
				ptr = ReadArgument(ptr,arg); //   ptr returns on next significant char
				if (*arg == '"' && stripQuotes)
				{
					size_t len = strlen(arg);
					if (arg[len-1] == '"') 
					{
						arg[len-1] = 0;
						memmove(arg,arg+1,strlen(arg));
					}
					// and purify internal \" to simple quote
					char* x = arg;
					while ((x = strchr(x,'\\')))
					{
						if (x[1] == '"') memmove(x,x+1,strlen(x)); // remove 
					}
				}
			}
			if (*arg == 0) // no argument found should not happen?
			{
				--callArgumentIndex;
				break;
			}

			//   within a function, seeing function argument as an argument (limit 9 calling Arguments)
			//   switch to incoming arg now, later callArgumentBase will be wrong
			if (*arg == '^' && IsDigit(arg[1]) ) strcpy(arg,callArgumentList[atoi(arg+1) + fnVarBase]); 
			if (*arg == '"' && arg[1] == ENDUNIT) // internal special quoted item, remove markers.
			{
				size_t len = strlen(arg);
				if (arg[len-2] == ENDUNIT)
				{
					arg[len-2] = 0;
					memmove(arg,arg+2,len-1);
				}
			}
			if (*arg == FUNCTIONSTRING && arg[1] == '"')
			{
				AllocateOutputBuffer();
				ReformatString(arg+2,currentOutputBase,result,0);
				strcpy(arg,currentOutputBase);
				FreeOutputBuffer();
			}
			if (!stricmp(arg,"null")) *arg = 0;	 // pass NOTHING as the value
			if ((trace & (TRACE_OUTPUT|TRACE_USERFN) || D->internalBits & TRACE_MACRO)  && CheckTopicTrace())
			{
				Log(STDUSERLOG, "%s",arg);
				if (*arg == '$') Log(STDUSERLOG,"(%s)",GetUserVariable(arg));
				else if (*arg == '_' && IsDigit(arg[1])) 
				{
					int id = GetWildcardID(arg);
					if (id >= 0) Log(STDUSERLOG,"(%s)",wildcardOriginalText[id]);
				}
				Log(STDUSERLOG, ", ");
			}
			++j;
		}
		while ((callArgumentIndex - oldArgumentIndex) < args) // fill in defaulted args to null
		{
			if ((trace & (TRACE_OUTPUT|TRACE_USERFN) || D->internalBits & TRACE_MACRO) && CheckTopicTrace()) Log(STDUSERLOG, "null, ");
			char* arg = callArgumentList[callArgumentIndex++];
			*arg = 0;
		}
		if (trace == TRACE_USERFN)  Log(STDUSERLOG, ") => ");
		else if ((trace & (TRACE_OUTPUT|TRACE_USERFN) || D->internalBits & TRACE_MACRO) && CheckTopicTrace()) Log(STDUSERLOG, ")\n");
		fnVarBase = callArgumentBase = oldArgumentIndex; 
	
		//   run the definition
		unsigned int oldtrace = trace;
		if (D->internalBits & TRACE_MACRO) trace = (unsigned int) -1;
		ChangeDepth(1,"HandleCall");
		if (result & ENDCODES){;}
		else if (callArgumentIndex >= (MAX_ARGUMENT_COUNT-1)) 	// pinned max (though we could legally arrive by accident on this last one)
		{
			ReportBug("User function nesting too deep %d",MAX_ARGUMENT_COUNT);
			result = FAILRULE_BIT;
		}
		else if ((D->internalBits & FUNCTION_BITS) == IS_PLAN_MACRO) result = PlanCode(D,buffer); // run a plan
		else if (definition)
		{
			ChangeDepth(1,"DoFunction");
			unsigned int flags = OUTPUT_FNDEFINITION;
			if (!(D->internalBits & IS_OUTPUT_MACRO)) flags|= OUTPUT_NOTREALBUFFER;// if we are outputmacro, we are merely extending an existing buffer
			Output((char*)definition,buffer,result,flags);
			ChangeDepth(-1,"DoFunction");
		}
		ChangeDepth(-1,"HandleCall");
		trace = oldtrace;
		fnVarBase = oldFnVarBase;
		if (callIndex) --callIndex; // safe decrement
		if (result & ENDCALL_BIT) result = (FunctionResult) (result ^ ENDCALL_BIT); // terminated user call 
	}

	//   pop argument list
	callArgumentIndex = oldArgumentIndex;	 
	callArgumentBase = oldArgumentBase;

	if ((trace & TRACE_OUTPUT || D->internalBits & TRACE_MACRO || (trace & TRACE_USERFN && definition)) && CheckTopicTrace()) 
	{
		if (trace == TRACE_USERFN)  Log(STDUSERLOG,"%s (%s) => %s\r\n",ResultCode(result),name,buffer);
		else if (info && info->properties & SAMELINE) Log(STDUSERLOG,"%s (%s) => %s\r\n",ResultCode(result),name,buffer);	// stay on same line to save visual space in log
		else Log(STDUSERTABLOG,"%s (%s) => %s\r\n",ResultCode(result),name,buffer);
	}
	if (D->internalBits & TRACE_MACRO) echo = oldecho; // allow eval call to change tracing status

	if (ptr && *ptr == ')') // skip ) and space if there is one...
	{
		if (ptr[1] == ' ') return ptr+2; // if this is a pattern comparison, this will NOT be a space, but will be a comparison op instead missing it
		return ptr+1;	// ptr to the end unit
	}
	else return ptr;
}

void DumpFunctions()
{
	unsigned int k = 0;
	SystemFunctionInfo *fn;
	while ( (fn = &systemFunctionSet[++k])  && fn->word )
	{
		if (*fn->word != '^') Log(STDUSERLOG,"%s\r\n",fn->word);
		else Log(STDUSERLOG,"%s - %s\r\n",fn->word,fn->comment);
	}
}

//////////////////////////////////////////////////////////
/// FUNCTION UTILITIES
//////////////////////////////////////////////////////////

char* ResultCode(FunctionResult result)
{
	char* ans = "OK";
	if (result & ENDCALL_BIT) ans = "ENDCALL";
	else if (result & ENDRULE_BIT) ans = "ENDRULE";
	else if (result & FAILRULE_BIT) ans = "FAILRULE";
	else if (result & RETRYRULE_BIT) ans = "RETRYRULE";
	else if (result & RETRYTOPRULE_BIT) ans = "RETRYTOPRULE";

	else if (result & ENDTOPIC_BIT) ans = "ENDTOPIC";
	else if (result & FAILTOPIC_BIT) ans = "FAILTOPIC";
	else if (result & RETRYTOPIC_BIT) ans = "RETRYTOPIC";

	else if (result & ENDSENTENCE_BIT) ans = "ENDSENTENCE";
	else if (result & FAILSENTENCE_BIT) ans = "FAILSENTENCE";
	else if (result & RETRYSENTENCE_BIT) ans = "RETRYSENTENCE";

	else if (result & RETRYINPUT_BIT) ans = "RETRYINPUT";
	else if (result & ENDINPUT_BIT) ans = "ENDINPUT";
	else if (result & FAILINPUT_BIT) ans = "FAILINPUT";
	else if (result & FAIL_MATCH) ans = "FAILMATCH";
	else if (result == NOPROBLEM_BIT) ans = "NOPROBLEM";
	else if (result == FAILLOOP_BIT) ans = "FAILLOOP";
	else if (result == ENDLOOP_BIT) ans = "ENDLOOP";
	else if (result & UNDEFINED_FUNCTION) ans = "UNDEFINED_FUNCTION";
	return ans;
};

 static void AddInput(char* buffer)
{
	char* copy = AllocateBuffer();
	strcpy(copy,nextInput);
	strcpy(nextInput," `` "); // system separator marks start of internal input
	char* ptr = nextInput + 4;
	unsigned int n = BurstWord(buffer);
	for (unsigned int i = 0; i < n; ++i)
	{
        strcpy(ptr,GetBurstWord(i));
		ptr += strlen(ptr);
		strcpy(ptr++," ");
	}
	strcpy(ptr," ` "); // mark end of internal input
	ptr += 3;
	strcpy(ptr,copy);
	FreeBuffer();
	if (strlen(nextInput) > 1000) nextInput[1000] = 0;	// overflow
}

static unsigned int ComputeSyllables(char* word)
{
	char copy[MAX_WORD_SIZE];
	MakeLowerCopy(copy,word);
	size_t len = strlen(copy);
	if (len <= 3) return 1;

	char* ptr = copy-1;
	unsigned int vowels = 0;
	int series = 0;
	while (*++ptr)
	{
		if (!IsVowel(*ptr)) 
		{
			if (series >= 4) --vowels; 
			series = 0;
		}
		else 
		{
			++vowels;
			++series;
		}
	}
	// silent e
	if (copy[len-1] == 'e' && !IsVowel(copy[len-2]) && IsVowel(copy[len-3])) --vowels;	// silent e
	
	// silent es or ed
	if ((copy[len-1] == 'd' || copy[len-1] == 's') && copy[len-2] == 'e' && !IsVowel(copy[len-3]) && IsVowel(copy[len-4])) --vowels;	// silent e

	return vowels;
}

static FunctionResult RandomMember(char* buffer,char* answer) 
{
#ifdef INFORMATION
returns a random member of a set or class

returns FAILRULE if a bad set is given.

The value is recursive. If the random member chosen is a set or class, the
link is followed and a random member from the next level is chosen, and so on. 
If the value is a wordnet reference it goes lower until it cant go any lower.

#endif
	MEANING members[3000];
loop:
	WORDP D = FindWord(answer);
	if (!D ) return FAILRULE_BIT;

    unsigned int count = 0;
    FACT* F = GetObjectHead(D);
    while (F && count < 2999)
    {
        if (F->verb == Mmember) members[count++] = F->subject;
        F = GetObjectNext(F);
    }
    if (!count) return FAILRULE_BIT; //   none found

	//   pick one at random
	while (ALWAYS)
	{
		MEANING M =  members[random(count)];
		M = GetMaster(M);
		D = Meaning2Word(M);
		unsigned int index = Meaning2Index(M);
		answer = D->word;
		if (*answer == '~') goto loop; //   member is a subset or class, get from it instead

		else if (index) // go down hierarchy until you cant and use that
		{
			FACT* F = GetObjectHead(D); // he is the general, get a specific
			count = 0;
			while (F && count < 2999)
			{
				if (F->verb == Mis && Meaning2Index(F->object) == index) members[count++] = F->subject;
				F = GetObjectNext(F);
			}
			if (count) continue; // select from there
			// we are a bottom meaning
			strcpy(buffer,D->word);
			return NOPROBLEM_BIT;
		}
		else break;
	}

    if (*answer == '<') ++answer; //   interjections have < in front
	strcpy(buffer,answer);
    return NOPROBLEM_BIT;
}

FunctionResult FLR(char* buffer,char* which)
{  
	unsigned int store;
	*buffer = 0;
	char word[MAX_WORD_SIZE];
	bool keep = false;
	char* ptr = ReadCompiledWord(ARGUMENT(1),word);
	if (!strnicmp(ptr,"KEEP",4)) keep = true;

	store = GetSetID(word);
	if (store == ILLEGAL_FACTSET) return FAILRULE_BIT;
	unsigned int count = FACTSET_COUNT(store);
	if (!count) 
	{
		if (impliedWild != ALREADY_HANDLED)
		{
			SetWildCardIndexStart(impliedWild);
			SetWildCard("","",0,0); // subject
			SetWildCard("","",0,0);	// verb
			SetWildCard("","",0,0);	// object
			SetWildCard("","",0,0);	// flags
		}
		impliedWild = ALREADY_HANDLED;
		return ENDRULE_BIT; //   terminates but does not cancel output
	}
	
	if (trace & TRACE_OUTPUT && CheckTopicTrace()) Log(STDUSERLOG,"[%d] => ",count);

	if (!withinLoop && planning && (*which != 'n') && *GetTopicName(currentTopicID) == '^' && !backtrackable) backtrackable = true;
	
	// pick fact
	unsigned int item;
	if (*which == 'l') item = count; //   last
	else if (*which == 'f') item = 1; //   first
	else if (*which == 'n') // next
	{
		item = ++factSetNext[store];
		if (count < item) return FAILRULE_BIT; 
	}
	else if (*which == 'r') item = random(count) + 1;    // random
	else // specific index
	{
		keep = true;
		item = atoi(which);
		if (count < item || item == 0) return FAILRULE_BIT;
	}
	FACT* F = factSet[store][item];

	// remove fact from set, but next does not alter set
	if (*which != 'n' && !keep)
	{
		SET_FACTSET_COUNT(store,(count-1));
		memmove(&factSet[store][item],&factSet[store][item+1],sizeof(FACT*) * (count - item)); 
	}		

	char type = *GetSetType(word);

	// transfer fact pieces appropriately
	MEANING Mfirst = 0;
	MEANING Mlast = 0;
	uint64 factSubject = 0;
	uint64 factObject = 0;
	if (trace & TRACE_INFER && CheckTopicTrace()) TraceFact(F);
	if (type == 'f') // want entire fact as index
	{
		if (impliedSet == ALREADY_HANDLED) sprintf(buffer,"%d",Fact2Index(F)); 
		else AddFact(impliedSet,F);
	}
	else if (type == 's') // want subject
	{
		if (!F) strcpy(buffer,"null");
		else
		{
			MEANING M = F->subject;
			if (F->flags & FACTSUBJECT) sprintf(buffer,"%d",M);
			else sprintf(buffer,"%s",Meaning2Word(M)->word);
		}
	}
	else if (type == 'v') // want verb
	{
		if (!F) strcpy(buffer,"null");
		else
		{
			MEANING M = F->verb;
			if (F->flags & FACTVERB) sprintf(buffer,"%d",M);
			else sprintf(buffer,"%s",Meaning2Word(M)->word);
		}
	}
	else if (type == 'o') // want object
	{
		if (!F) strcpy(buffer,"null");
		else
		{
			MEANING M = F->object;
			if (F->flags & FACTOBJECT) sprintf(buffer,"%d",M);
			else sprintf(buffer,"%s",Meaning2Word(M)->word);
		}
	}
	else if ( type == 'a' || type == '+'  || type == ' ' || !type || type == 'r') // want all, subject first
	{
		if (!F) Mfirst = Mlast = 0xffffffff;
		else
		{
			Mfirst = F->subject;
			factSubject = F->flags & FACTSUBJECT;
			Mlast = F->object;
			factObject = F->flags & FACTOBJECT;
		}
	}
	else // want all, object first
	{
		if (!F) Mfirst = Mlast = 0xffffffff;
		else
		{
			Mlast = F->subject;
			factObject = F->flags & FACTSUBJECT;
			Mfirst = F->object;
			factSubject= F->flags & FACTOBJECT;
		}
	}
	if (Mfirst) // spread
	{
		char factID[100];
		char* piece;
		if ( Mfirst == 0xffffffff) piece = "null";
		else if (factSubject) 
		{
			sprintf(factID,"%d",Mfirst);
			piece = factID;
		}
		else if (type == 'r') piece = WriteMeaning(Mfirst,false);
		else piece = Meaning2Word(Mfirst)->word;

		// _wildcard can take all, otherwise you get just a field
		// for variables. not legal for sets

		if (impliedWild == ALREADY_HANDLED) strcpy(buffer,piece);
		else 
		{
			SetWildCardIndexStart(impliedWild);
			if (trace & TRACE_INFER && CheckTopicTrace()) Log(STDUSERLOG," _%d=%s ",impliedWild,piece);
			SetWildCard(piece,piece,0,0); 

			 //   verb 
			if ( Mfirst == 0xffffffff) piece = "null";
			else
			{
				MEANING M = F->verb;
				if (F->flags & FACTVERB) 
				{
					sprintf(factID,"%d",M);
					piece = factID;
				}
				else if (type == 'r') piece = WriteMeaning(M,false);
				else piece = Meaning2Word(M)->word;
			}
			if (trace & TRACE_INFER && CheckTopicTrace()) Log(STDUSERLOG," _%d=%s ",impliedWild+1,piece);
			SetWildCard(piece,piece,0,0);

			//   object
			if ( Mfirst == 0xffffffff) piece = "null";
			else if (factObject) 
			{
				sprintf(factID,"%d",Mlast);
				piece = factID;
			}
			else if (type == 'r') piece = WriteMeaning(Mlast,false);
			else piece = Meaning2Word(Mlast)->word;
			if (trace & TRACE_INFER && CheckTopicTrace()) Log(STDUSERLOG," _%d=%s ",impliedWild+2,piece);
			SetWildCard(piece,piece,0,0); 

			if ( type == 'a' && F) // all include flags on fact
			{
				sprintf(tmpWord,"0x%08x",F->flags);
				SetWildCard(tmpWord,tmpWord,0,0);
			}
		}
		impliedSet = impliedWild = ALREADY_HANDLED; // we spread the values out
	}
	if (trace & TRACE_OUTPUT && *buffer && CheckTopicTrace()) Log(STDUSERLOG," %s  ",buffer);
	return NOPROBLEM_BIT;
}

bool RuleTest(char* data) // see if pattern matches
{
	char pattern[MAX_WORD_SIZE];
	GetPattern(data,NULL,pattern);
	unsigned int gap = 0;
	unsigned int wildcardSelector = 0;
	wildcardIndex = 0;
	unsigned int junk;
	bool uppercasem = false;
	int matched = 0;
	bool answer =  Match(pattern+2,0,0,'(',true,gap,wildcardSelector,junk,junk,uppercasem,matched); // start past the opening paren
	return answer;
}

unsigned int Callback(WORDP D,char* arguments) 
{
	if (! D || !(D->internalBits & FUNCTION_NAME)) return FAILRULE_BIT;
	unsigned int oldtrace = trace;
	trace = 0;
	char args[MAX_WORD_SIZE];
	strcpy(args,arguments);
	FunctionResult result;
	AllocateOutputBuffer();
	DoFunction(D->word,args,currentOutputBase,result);
	FreeOutputBuffer();
	trace = oldtrace;
	return result;
}

void ResetUser(char* input)
{
	unsigned int oldtopicid = currentTopicID;
	char* oldrule = currentRule;
	int oldruleid = currentRuleID;
	int oldruletopic = currentRuleTopic;
	ResetToPreUser();	// back to empty state before user
	KillShare();
	ReadNewUser(); 
	userFirstLine = 1;
	responseIndex = 0;
	wasCommand = BEGINANEW;
	*input = 0;
	currentTopicID = oldtopicid;
	currentRule = oldrule;
	currentRuleID = oldruleid;
	currentRuleTopic = oldruletopic;
}

//////////////////////////////////////////////////////////
/// TOPIC FUNCTIONS
//////////////////////////////////////////////////////////

static FunctionResult AddTopicCode(char* buffer) 
{     
	AddPendingTopic(FindTopicIDByName(ARGUMENT(1))); // does not fail, just may not become pending
	return NOPROBLEM_BIT;
}

static FunctionResult ClearTopicsCode(char* buffer)
{
	ClearPendingTopics();
	return NOPROBLEM_BIT;
}

static FunctionResult CountTopicCode(char* buffer) 
{     
	int topic = FindTopicIDByName(ARGUMENT(1));
	if (BlockedBotAccess(topic)) return FAILRULE_BIT;
	topicBlock* block = TI(topic);

	char* name = ARGUMENT(2);
	if (!strnicmp(name,"gambit",6)) sprintf(buffer,"%d", GAMBIT_MAX(block->topicMaxRule)); 
	else if (!strnicmp(name,"rule",4)) sprintf(buffer,"%d", RULE_MAX(block->topicMaxRule)); 
	else if (!stricmp(name,"used")) sprintf(buffer,"%d",TopicUsedCount(topic));
	else if (!stricmp(name,"available"))
	{
		unsigned int count = 0;
		unsigned int* map = block->gambitTag;	
		unsigned int gambitID = *map;
		while (gambitID != NOMORERULES)
		{
			if (UsableRule(topic,gambitID)) ++count;
			gambitID = *++map;
		}
		sprintf(buffer,"%d",count); 
	}
	else return FAILRULE_BIT;
	return NOPROBLEM_BIT;
}

static FunctionResult GambitCode(char* buffer) 
{ 
	if (planning) return FAILRULE_BIT;	// cannot call from planner
	char* arg2 = ARGUMENT(2);
	if (*arg2 != 0 && stricmp(arg2,"FAIL")) 
		return FAILRULE_BIT; // bad 2nd arg

	// gambit(PENDING) means from interesting stack  
	// gambit(~name) means use named topic 
	// gambit(~) means current topic we are within now
	// gambit (word) means topic with that keyword
	// if a second argument exists (FAIL) then return failure code if doesnt generate
	unsigned int oldIndex = responseIndex;
	if (all) return FAILRULE_BIT; // dont generate gambits when doing all

	//  if "~", get current topic name to use for gambits
	char* word = ARGUMENT(1);
	unsigned int topic;
	FunctionResult result = FAILRULE_BIT;
	
	int oldreuseid = currentReuseID;
	unsigned int oldreusetopic = currentReuseTopic;
	currentReuseID = currentRuleID; // LOCAL reuse
	currentReuseTopic = currentRuleTopic;

   	if (!stricmp(word,"pending")) // pick topic from pending stack
	{
		unsigned int stack[MAX_TOPIC_STACK+1];
		memcpy(stack,pendingTopicList,pendingTopicIndex * sizeof(unsigned int)); // copy stack
		int oldCurrentTopic = currentTopicID;
		int oldPendingIndex = pendingTopicIndex;
        while (oldPendingIndex) // walk topics, most recent first
		{
			unsigned int topic = stack[--oldPendingIndex];
			char* xname = GetTopicName(currentTopicID); // just for debugging
			if (TopicInUse(topic) == -1) continue;
			currentTopicID = topic;
			ChangeDepth(1,"GambitCode");
			FunctionResult myresult = PerformTopic(GAMBIT,buffer);
			ChangeDepth(-1,"GambitCode");
			if (myresult & RESULTBEYONDTOPIC) 
			{
				result = myresult;
				break;
			}
			if (responseIndex > oldIndex) 
			{
				result = NOPROBLEM_BIT;
				break;
			}
		}
		currentTopicID = oldCurrentTopic; // this is where we were
	}

	 // do topic by name
	else if (*word == '~')
	{
		topic = FindTopicIDByName(word);
		if (topic && !(GetTopicFlags(topic) & TOPIC_BLOCKED))
		{
 			int pushed = PushTopic(topic);
			if (pushed < 0) result =  FAILRULE_BIT;
			else 
			{
				ChangeDepth(1,"GambitCode1");
				result = PerformTopic(GAMBIT,buffer);
				ChangeDepth(-1,"GambitCode1");

				if (pushed) PopTopic();
			}
		}
		if (!result && !stricmp(arg2,"FAIL") && responseIndex <= oldIndex)  result = FAILRULE_BIT; // report failure
	}
	
	// do topic by keyword
	else
	{
		WORDP D = FindWord(word);
		FACT* F = NULL;
		if (!D) result = NOPROBLEM_BIT;
		else  F = GetSubjectHead(D);
		while (F) // find topics word is a direct member of
		{
			if (F->verb == Mmember)
			{
				WORDP E = Meaning2Word(F->object);
				if (E->internalBits & TOPIC)
				{
					unsigned int topic = FindTopicIDByName(E->word);
					if (topic && !(GetTopicFlags(topic) & (TOPIC_BLOCKED|TOPIC_SYSTEM|TOPIC_NOGAMBITS)))
					{
 						int pushed = PushTopic(topic);
						if (pushed < 0) 
						{
							result = FAILRULE_BIT;
							break;
						}
						ChangeDepth(1,"GambitCode2");
						result = PerformTopic(GAMBIT,buffer);
						ChangeDepth(-1,"GambitCode2");
						if (pushed) PopTopic();
						if (result & RESULTBEYONDTOPIC) break;
						if (responseIndex > oldIndex)  
						{
							result = NOPROBLEM_BIT;
							break;
						}
					}
				}
			}
			F = GetSubjectNext(F);
		} 
		if (!stricmp(arg2,"FAIL"))  result = FAILRULE_BIT; // report failure
	}
	currentReuseID = oldreuseid;
	currentReuseTopic = oldreusetopic;

	return result;
}

static FunctionResult GetVerifyCode(char* buffer) 
{
	char* arg1 = ARGUMENT(1);
	unsigned int topicid;
	int id;
	char* verify = GetVerify(arg1,topicid,id); //  ~topic.#.#=LABEL<~topic.#.#  is a maximally complete why
	if (verify) strcpy(buffer,verify);
	return NOPROBLEM_BIT;
}

static FunctionResult GetRuleCode(char* buffer) 
{     
	char* arg1 = ARGUMENT(1);
	char* arg2 = ARGUMENT(2);
	char* arg3 = ARGUMENT(3);
	unsigned int topic = currentTopicID;
	int id;
	char* rule;
	bool fulllabel = false;
	bool crosstopic = false;
	char* dot = strchr(arg2,'.');
	if (dot && IsDigit(dot[1])) rule = GetRuleTag(topic,id,arg2);
	else rule = GetLabelledRule(topic,arg2,arg3,fulllabel,crosstopic,id,currentTopicID);
	if (!rule) return FAILRULE_BIT;
	if (!stricmp(arg1,"tag")) sprintf(buffer,"%s.%d.%d",GetTopicName(topic),TOPLEVELID(id),REJOINDERID(id));
	else if (!stricmp(arg1,"topic")) strcpy(buffer,GetTopicName(topic));
	else if (!stricmp(arg1,"label")) GetLabel(rule,buffer);
	else if (!stricmp(arg1,"type")) sprintf(buffer,"%c",*rule);
	else if (!stricmp(arg1,"pattern")) // use pattern notation so it can work with ^match and will not be harmed stored as a variable
	{
		*buffer = '"';
		buffer[1] = 0;
		GetPattern(rule,NULL,buffer+1);
		if (!buffer[1]) *buffer = 0;
		else strcat(buffer,"\"");
	}
	else if (!stricmp(arg1,"usable")) strcpy(buffer,(UsableRule(topic,id)) ? (char*) "1" : (char*) "");
	else // output
	{
		 rule = GetPattern(rule,NULL,NULL);
		 char* end = strchr(rule,ENDUNIT);  // will not be a useful output as blanks will become underscores, but can do ^reuse() to execute it
		 *end = 0;
		 strcpy(buffer,rule);
		 *end = ENDUNIT;
	}
	if (trace & TRACE_OUTPUT && CheckTopicTrace())
	{
		char word[MAX_WORD_SIZE];
		strncpy(word,buffer,50);
		word[50] = 0;
		Log(STDUSERLOG," %s ",word);
	}
	return NOPROBLEM_BIT;
}
	
static FunctionResult HasGambitCode(char* buffer)
{
	// hasgambit(~topic) means does it have any unused gambits
	// hasgambit(~topic last) means is last gambit unused
	// hasgambit(~topic any) means does it have gambits used or unused
	char* name = ARGUMENT(1);
	unsigned int topic = FindTopicIDByName(name);
	if (!topic) return FAILRULE_BIT;
	topicBlock* block = TI(topic);

	unsigned int gambits = GAMBIT_MAX(block->topicMaxRule);   // total gambits of topic
	if (!gambits) return FAILRULE_BIT;	

	char* arg = ARGUMENT(2);
	if (!stricmp(arg,"last")) return UsableRule(topic,block->gambitTag[gambits-1]) ? NOPROBLEM_BIT : FAILRULE_BIT; // is last gambit unused
	else if (!stricmp(arg,"any")) return NOPROBLEM_BIT;
	else return (HasGambits(topic) < 1) ? FAILRULE_BIT : NOPROBLEM_BIT;
}

static FunctionResult KeepCode(char* buffer)
{
	if (planning) return FAILRULE_BIT;

	AddKeep(currentRule);
	return NOPROBLEM_BIT;
}

static FunctionResult LastUsedCode(char* buffer)
{
	char* name = ARGUMENT(1);
	char* what = ARGUMENT(2);
	unsigned int topic = FindTopicIDByName(name);
	if (!topic)  return FAILRULE_BIT;  
	topicBlock* block = TI(topic);

	if (!strnicmp(what,"gambit",6)) sprintf(buffer,"%d",block->topicLastGambitted);
	else if (!strnicmp(what,"responder",8)) sprintf(buffer,"%d",block->topicLastRespondered);
	else if (!strnicmp(what,"rejoinder",6)) sprintf(buffer,"%d",block->topicLastRejoindered);
	else // any 
	{
		unsigned int last = block->topicLastRejoindered;
		if (block->topicLastRespondered > last) last = block->topicLastRespondered;
		if (block->topicLastGambitted > last) last = block->topicLastGambitted;
		sprintf(buffer,"%d",last);
	}
	return NOPROBLEM_BIT;
}

static FunctionResult PopTopicCode(char* buffer) // reconsider BUG
{     
	char* arg1 = ARGUMENT(1);
	if (*arg1 == '~') RemovePendingTopic(FindTopicIDByName(arg1)); // current topic may continue executing
	else if (!*arg1) // make current topic not interesting AND quit it
	{
		RemovePendingTopic(currentTopicID);
		return ENDTOPIC_BIT; 
	}
	else return FAILRULE_BIT;
	return NOPROBLEM_BIT;
}

static FunctionResult RefineCode(char* buffer) 
{
	FunctionResult result = NOPROBLEM_BIT;
 
	char* arg1 = ARGUMENT(1); // nothing or FAIL or label of rule or topic.label
	char* arg2 = ARGUMENT(2); 
	bool fail = false;
	if (!stricmp(arg1,"FAIL")) 
	{
		fail = true; 
		strcpy(arg1,arg2); // promote any 2nd argument
	}
	
	char* rule;
    int id = currentRuleID;
	unsigned int topic = currentTopicID;
	if (!*ARGUMENT(1)) rule = FindNextRule(NEXTRULE,currentRule,id); // default continue AFTER the current rule
	else // designated
	{
		bool fulllabel = false;
		bool crosstopic = false;
		char* dot = strchr(arg1,'.');
		if (dot && IsDigit(dot[1])) rule = GetRuleTag(topic,id,arg1);
		else rule = GetLabelledRule(topic,arg1,"",fulllabel,crosstopic,id,currentTopicID);
	}

	if (!rule) return FAILRULE_BIT;

	// change context now
	SAVEOLDCONTEXT()
	currentRule = rule;
	currentRuleTopic = currentTopicID = topic;
	currentRuleID = id;
	char level = *currentRule;
	while (currentRule && level == *currentRule) // try all choices
    {
		if (trace & TRACE_PATTERN && CheckTopicTrace())
		{
			char label[MAX_WORD_SIZE];
			GetLabel(currentRule,label);
			if (*label) Log(STDUSERTABLOG, "try %s: \\",label); // the \\ will block linefeed on next Log call
			else Log(STDUSERTABLOG, "try  \\");
		}
		ChangeDepth(1,"RefineCode");
 		result = TestRule(id,currentRule,buffer);
		ChangeDepth(-1,"RefineCode");
	    if (result != FAIL_MATCH) break;
		else result = NOPROBLEM_BIT;

		while (currentRule && *currentRule)
		{
			currentRule = FindNextRule(NEXTRULE,currentRule,id); 
			if (currentRule && (*currentRule <= level  || !Rejoinder(currentRule))) break;	// matches our level OR is earlier than it (end of a zone like refine of a: into b: zone)
		}
    }
	if (outputRejoinderRuleID == NO_REJOINDER) outputRejoinderRuleID = BLOCKED_REJOINDER; // refine values exist instead of real rejoinders, dont let calling rule do set rejoinder
	RESTOREOLDCONTEXT()
	if ((!currentRule || level != *currentRule) && fail) result = FAILRULE_BIT;
	return result; // finding none does not fail unless told to fail
}

static FunctionResult RejoinderCode(char* buffer)
{ 
	if (postProcessing)
	{
		ReportBug("Not legal to use ^rejoinder in postprocessing");
		return FAILRULE_BIT;
	}
    if (!unusedRejoinder) 
	{
		if (trace & TRACE_BASIC && CheckTopicTrace()) Log(STDUSERLOG," disabled rejoinder\r\n\r\n");
		return NOPROBLEM_BIT; //   an earlier response handled this
	}

	if (*ARGUMENT(1)) // 
	{
		char* tag = ARGUMENT(1);
		unsigned int topic = currentTopicID;
		bool fulllabel = false;
		bool crosstopic = false;
		char* rule;
		char* dot = strchr(tag,'.');
		int id;
		if (dot && IsDigit(dot[1])) rule = GetRuleTag(topic,id,tag);
		else rule = GetLabelledRule(topic,tag,"",fulllabel,crosstopic,id,currentTopicID);
		if (!rule) return FAILRULE_BIT; // unable to find labelled rule 

		char level = TopLevelRule(rule)   ? 'a' :  (*rule+1); // default rejoinder level
		char* ptr = FindNextRule(NEXTRULE,rule,id);
		while (ptr && *ptr && !TopLevelRule(ptr)) //  walk units til find level matching
		{
			if (*ptr == level) break;     //   found desired starter
			if (*ptr < level) return FAILRULE_BIT; // there is no rejoinder for us
		}
		if (!ptr || *ptr != level) return FAILRULE_BIT;		// not found

		inputRejoinderRuleID = id; 
 		inputRejoinderTopic = currentTopicID;
	}

	if (inputRejoinderRuleID == NO_REJOINDER) 
	{
		if (trace & TRACE_PATTERN && CheckTopicTrace()) Log(STDUSERLOG,"  rejoinder not set\r\n");
		return NOPROBLEM_BIT; // not a failure, just nothing done
	}

    //   we last made a QUESTIONWORD or statement, can his reply be expected for that? 
	FunctionResult result = NOPROBLEM_BIT;
	int pushed = PushTopic(inputRejoinderTopic);
	if (pushed < 0) return FAILRULE_BIT;
	
    char* ptr = GetRule(inputRejoinderTopic,inputRejoinderRuleID);
    if (!ptr)  
	{
		if (trace & TRACE_BASIC && CheckTopicTrace()) Log(STDUSERLOG," no rejoinder data for topic %s %d.%d\r\n\r\n",GetTopicName(currentTopicID),TOPLEVELID(inputRejoinderRuleID),REJOINDERID(inputRejoinderRuleID));
		if (pushed) PopTopic();
		return result;
	}

	unsigned int oldtrace = trace;
	if (trace & TRACE_BASIC && CheckTopicTrace()) 
	{
		Log(STDUSERLOG,"  try rejoinder for: %s %d.%d",GetTopicName(currentTopicID),TOPLEVELID(inputRejoinderRuleID),REJOINDERID(inputRejoinderRuleID));
	}
	int id = inputRejoinderRuleID;
	
    char level[400];
    char word[MAX_WORD_SIZE];
    ReadCompiledWord(ptr,level); //   what marks this level
	ChangeDepth(1,"RejoinderCode");
    while (ptr && *ptr) //   loop will search for a level answer it can use
    {
        ReadCompiledWord(ptr,word); // read responder type
        if (!*word) break; //   no more data
        if (TopLevelRule(word)) break; // failed to find rejoinder
        else if (*word < *level) break;  // end of local choices
        else if (!stricmp(word,level)) // check rejoinder
        {
			result = TestRule(id,ptr,buffer);
			if (result == FAIL_MATCH) result = FAILRULE_BIT; // convert 
			if (result == NOPROBLEM_BIT) // we found a match
			{
				unusedRejoinder = false;
				break; 
			}
			if (result & (RETRYTOPIC_BIT|RETRYSENTENCE_BIT|FAILTOPIC_BIT|ENDTOPIC_BIT|FAILSENTENCE_BIT|ENDSENTENCE_BIT|ENDINPUT_BIT|RETRYINPUT_BIT)) break;
			result = NOPROBLEM_BIT;
        }
       ptr = FindNextRule(NEXTRULE,ptr,id); //   wrong or failed responder, swallow this subresponder whole
    }
	if (pushed) PopTopic(); 
	ChangeDepth(-1,"RejoinderCode");

    if (inputSentenceCount) // this is the 2nd sentence that failed, give up
    {   
        inputRejoinderRuleID = NO_REJOINDER;
        unusedRejoinder = false;
    }
    trace = oldtrace;
	return  (FunctionResult) (result & (-1 ^ (ENDRULE_BIT | FAILRULE_BIT | RETRYRULE_BIT | RETRYTOPRULE_BIT )));
}

static FunctionResult RespondCode(char* buffer)
{  // failing to find a responder is not failure unless ask it to be

	if (planning) return FAILRULE_BIT;	// cannot call from planner

	char* name = ARGUMENT(1);
	char* rule = NULL;
	char* dot = strchr(name,'.'); // tagged?
	if (dot) *dot = 0;
	unsigned int topic = FindTopicIDByName(name); // handles ~ and fully named topics
	if (dot) *dot = '.';
	int id = 0;
	if (dot) // find tagged rule
	{
		bool fulllabel = false;
		bool crosstopic = false;
		if (IsDigit(dot[1])) rule = GetRuleTag(topic,id,name); // numbered rule
		else rule = GetLabelledRule(topic,name,"",fulllabel,crosstopic,id,topic); // labelled rule
		if (!rule) return FAILRULE_BIT; // unable to find labelled rule 
	}

	// respond(PENDING) means from interesting stack  
	// respond(~name) means use named topic 
	// respond(~) means current topic we are within now
	// respond(word) means topic with that keyword
	// if a second argument exists (FAIL) then return failure code if doesnt generate output to user
	unsigned int oldIndex = responseIndex;
	char* word = ARGUMENT(1);
	FunctionResult result = FAILRULE_BIT;
	
	int oldreuseid = currentReuseID;
	unsigned int oldreusetopic = currentReuseTopic;
	currentReuseID = currentRuleID; // LOCAL reuse
	currentReuseTopic = currentRuleTopic;

   	if (!stricmp(word,"pending")) // pick topic from pending stack
	{
		unsigned int stack[MAX_TOPIC_STACK+1];
		memcpy(stack,pendingTopicList,pendingTopicIndex * sizeof(unsigned int)); // copy stack
		int oldCurrentTopic = currentTopicID;
		int oldPendingIndex = pendingTopicIndex;
        while (oldPendingIndex) // walk topics, most recent first
		{
			unsigned int topic = stack[--oldPendingIndex];
			char* xname = GetTopicName(currentTopicID); // just for debugging
			if (TopicInUse(topic) == -1) continue;
			currentTopicID = topic;
			ChangeDepth(1,"GambitCode");
			FunctionResult myresult = PerformTopic(0,buffer);
			ChangeDepth(-1,"GambitCode");
			if (myresult & RESULTBEYONDTOPIC)
			{
				result = myresult;
				break;
			}
			if (responseIndex > oldIndex) 
			{
				result = NOPROBLEM_BIT;
				break;
			}
		}
		currentTopicID = oldCurrentTopic;
	}

	 // do topic by name
	else if (*word == '~')
	{
		char* arg2 = ARGUMENT(2);
		unsigned oldIndex = responseIndex;
		if (!topic)  return FAILRULE_BIT; 
		if (GetTopicFlags(topic) & TOPIC_BLOCKED) 
		{
			if (!stricmp(arg2,"FAIL") && responseIndex <= oldIndex)  return FAILRULE_BIT; // report failure
			return NOPROBLEM_BIT;
		}
		unsigned int oldTopic = currentTopicID;
		int pushed =  PushTopic(topic); 
		if (pushed < 0) return FAILRULE_BIT;
		ChangeDepth(1,"RespondCode");
		result = PerformTopic(0,buffer,rule,id);
		ChangeDepth(-1,"RespondCode");
		if (pushed) PopTopic();

		AddKeep(currentRule);  //   do not allow responders to erase his nest call whether or not he succeeds  BUG ???
		result = (FunctionResult)(result & (-1 ^ (ENDTOPIC_BIT|ENDRULE_BIT))); // these are swallowed
		currentTopicID = oldTopic;
		if (result == NOPROBLEM_BIT && !stricmp(arg2,"FAIL") && responseIndex <= oldIndex)  result = FAILRULE_BIT; // report failure
	}
	
	// do topic by keyword
	else
	{
		WORDP D = FindWord(word);
		FACT* F = NULL;
		if (!D) result = NOPROBLEM_BIT;
		else  F = GetSubjectHead(D);
		unsigned int oldTopic = currentTopicID;
		while (F) // find topics word is a direct member of
		{
			if (F->verb == Mmember)
			{
				WORDP E = Meaning2Word(F->object);
				if (E->internalBits & TOPIC)
				{
					unsigned int topic = FindTopicIDByName(E->word);
					if (topic && !(GetTopicFlags(topic) & (TOPIC_BLOCKED|TOPIC_SYSTEM|TOPIC_NOGAMBITS)))
					{
 						int pushed = PushTopic(topic);
						if (pushed < 0) 
						{
							result = FAILRULE_BIT;
							break;
						}
						ChangeDepth(1,"RespondCode2");
						result = PerformTopic(0,buffer);
						ChangeDepth(-1,"RespondCode2");
						if (pushed) PopTopic();
						if (result & RESULTBEYONDTOPIC) break;
						if (responseIndex > oldIndex)  
						{
							result = NOPROBLEM_BIT;
							break;
						}
					}
				}
			}
			F = GetSubjectNext(F);
		} 

		AddKeep(currentRule);  //   do not allow responders to erase his nest call whether or not he succeeds  BUG ???
		result = (FunctionResult)(result & (-1 ^ (ENDTOPIC_BIT|ENDRULE_BIT))); // these are swallowed
		currentTopicID = oldTopic;
		if (!stricmp(ARGUMENT(2),"FAIL") && responseIndex <= oldIndex)  result = FAILRULE_BIT; // report failure
	}
	return result;
}

void ResetReuseSafety()
{
	memset(reuseSafety,0,sizeof(reuseSafety));
	memset(reuseSafetyCount,0,sizeof(reuseSafety));
	reuseIndex = 0;
}

static FunctionResult ReuseCode(char* buffer) 
{ 
	int id = 0;
	char* arg1 = ARGUMENT(1); // label of rule or topic.label
	if (!*arg1) return FAILRULE_BIT;

	unsigned int topic = currentTopicID;
	bool fulllabel = false;
	bool crosstopic = false;
	char* arg2 = ARGUMENT(2); // optional- if there not allowed to use erased rules
	char* arg3 = ARGUMENT(3); // possible fail value
	if (!stricmp(arg2,"FAIL")) // make it 3rd argument if it exists
	{
		strcpy(arg2,arg3);
		strcpy(arg3,"FAIL");
	}

	char* rule;
	char* dot = strchr(arg1,'.');
	if (dot && IsDigit(dot[1])) rule = GetRuleTag(topic,id,arg1);
	else rule = GetLabelledRule(topic,arg1,arg2,fulllabel,crosstopic,id,currentTopicID);
	if (!rule) return FAILRULE_BIT; // unable to find labelled rule 

	bool found = false;
	for (unsigned int i = 0; i <= MAX_REUSE_SAFETY; ++i)
	{
		if (reuseSafety[i] == rule) 
		{
			found = true;
			if (++reuseSafetyCount[i] > 10)
			{
				char c = rule[30];
				rule[30] = 0;
				ReportBug("Recursive reuse %s",rule);
				rule[30] = c;
				return FAILRULE_BIT;
			}
			else break;
		}
	}
	if (!found)
	{
		reuseSafetyCount[reuseIndex] = 0;
		reuseSafety[reuseIndex++] = rule;
	}
	if (reuseIndex == MAX_REUSE_SAFETY) reuseIndex = 0;

	int oldreuseid = currentReuseID;
	unsigned int oldreusetopic = currentReuseTopic;

	currentReuseID = currentRuleID; // LOCAL reuse
	currentReuseTopic = currentRuleTopic;

	// execute rule 
	SAVEOLDCONTEXT()
	currentRule = rule;
	currentRuleID = id;
	currentRuleTopic = currentTopicID = topic;
	
	unsigned int holdindex = responseIndex;
	ChangeDepth(1,"reuseCode");
	FunctionResult result = ProcessRuleOutput(currentRule,currentRuleID,buffer); 
	ChangeDepth(-1,"reuseCode");
	if (crosstopic && responseIndex > holdindex) AddPendingTopic(topic); // restore caller topic as interesting
	RESTOREOLDCONTEXT()
	currentReuseID = oldreuseid;
	currentReuseTopic = oldreusetopic;

	if (trace & TRACE_OUTPUT && CheckTopicTrace()) Log(STDUSERTABLOG,""); //   restore index from lower level
	if (!result && holdindex == responseIndex && !stricmp(arg3,"FAIL")) return FAILRULE_BIT; // user wants notification of failure
	return result;
}

static FunctionResult AvailableCode(char* buffer) 
{ 
	int id = 0;
	char* arg1 = ARGUMENT(1); // label of rule or topic.label
	if (!*arg1) return FAILRULE_BIT;

	unsigned int topic = currentTopicID;
	bool fulllabel = false;
	bool crosstopic = false;
	char* rule;
	char* dot = strchr(arg1,'.');
	if (dot && IsDigit(dot[1])) rule = GetRuleTag(topic,id,arg1);
	else rule = GetLabelledRule(topic,arg1,"",fulllabel,crosstopic,id,currentTopicID);
	if (!rule) return FAILRULE_BIT; // unable to find labelled rule 
	unsigned int result = UsableRule(topic,id);
	if (!result && !stricmp(ARGUMENT(2),"FAIL")) return FAILRULE_BIT; // user wants notification of failure
	sprintf(buffer,"%d",result);
	return NOPROBLEM_BIT;
}

static FunctionResult SetRejoinderCode(char* buffer)
{
	if (planning) return NOPROBLEM_BIT; // canot rejoinder inside a plan
	bool input = false;
	char* tag = ARGUMENT(1);
	if (!*ARGUMENT(2)){;}
	else if (!stricmp(tag,"input")) input = true;
	else if (!stricmp(tag,"output")) {;}
	else return FAILRULE_BIT;
	if (*ARGUMENT(2)) tag = ARGUMENT(2);

	unsigned int topic = currentTopicID;
	bool fulllabel = false;
	bool crosstopic = false;
	char* rule;
	char* dot = strchr(tag,'.');
	int id;
	if (dot && IsDigit(dot[1])) rule = GetRuleTag(topic,id,tag);
	else rule = GetLabelledRule(topic,tag,"",fulllabel,crosstopic,id,currentTopicID);
	if (!rule) return FAILRULE_BIT; // unable to find labelled rule 

	char level = TopLevelRule(rule)   ? 'a' :  (*rule+1); // default rejoinder level
	char* ptr = FindNextRule(NEXTRULE,rule,id);
    while (ptr && *ptr && !TopLevelRule(ptr)) //  walk units til find level matching
    {
        if (*ptr == level) break;     //   found desired starter
        if (*ptr < level) return FAILRULE_BIT; // there is no rejoinder for us
    }
	if (!ptr || *ptr != level) return FAILRULE_BIT;		// not found

	if (input)
	{
		inputRejoinderRuleID = id; 
 		inputRejoinderTopic = currentTopicID;
		if (trace & TRACE_OUTPUT && CheckTopicTrace()) Log(STDUSERLOG,"  **set input rejoinder at %s.%d.%d\r\n",tag,TOPLEVELID(id),REJOINDERID(id));
	}
	else
	{
		outputRejoinderRuleID = id; 
 		outputRejoinderTopic = currentTopicID;
		if (trace & TRACE_OUTPUT && CheckTopicTrace()) Log(STDUSERLOG,"  **set output rejoinder at %s.%d.%d\r\n",tag,TOPLEVELID(id),REJOINDERID(id));
	}
	return NOPROBLEM_BIT;
}

static FunctionResult TopicFlagsCode(char* buffer)
{
	sprintf(buffer,"%d",GetTopicFlags(FindTopicIDByName(ARGUMENT(1))));
	return NOPROBLEM_BIT;
}

//////////////////////////////////////////////////////////
/// TOPIC LISTS
//////////////////////////////////////////////////////////

static FunctionResult GetTopicsWithGambitsCode(char* buffer)
{ 
	unsigned int store = (impliedSet == ALREADY_HANDLED) ? 0 : impliedSet;
	SET_FACTSET_COUNT(store,0);
	*buffer = 0;

    for (unsigned int topicid = 1; topicid <= numberOfTopics; ++topicid) 
    {
        if (topicid == currentTopicID || HasGambits(topicid) <= 0) continue;
		if (GetTopicFlags(topicid) & TOPIC_NOGAMBITS) continue;	// dont use this
		char* name = GetTopicName(topicid);
		if (!*name) continue; // deactivated by faketopic
		MEANING T = MakeMeaning(StoreWord(name));
		FACT* F = CreateFact(T, MgambitTopics,T,FACTTRANSIENT);
		AddFact(store,F);
	}
	if (impliedSet == ALREADY_HANDLED && FACTSET_COUNT(store) == 0) return FAILRULE_BIT;
	impliedSet = impliedWild = ALREADY_HANDLED;	
	return NOPROBLEM_BIT;
}

static int OrderTopics(unsigned short topicList[MAX_TOPIC_KEYS],unsigned int matches[MAX_TOPIC_KEYS]) // find other topics that use keywords
{
	bool newpass = topicList[1] != 0;
	unsigned int max = 2;
    unsigned int index = 0;
    unsigned int i;
	char currentTopic[MAX_WORD_SIZE];
	GetActiveTopicName(currentTopic); // current topic, not system or nostay.
	unsigned int baseid = FindTopicIDByName(currentTopic);

	//  value on each topic
    for (i = 1; i <= numberOfTopics; ++i) // value 0 means we havent computed it yet. Value 1 means it has been erased.
    {
		if (i == baseid || BlockedBotAccess(i)) continue;

        char* name = GetTopicName(i);
		if (!*name) continue; // hidden topic
	    unsigned int val = topicList[i];
        if (!val) //   compute match value
        {
            char word[MAX_WORD_SIZE];
            strcpy(word,name);
			char* dot = strchr(word+1,DUPLICATETOPICSEPARATOR);
			if (dot) *dot = 0;	// use base name of the topic, not topic family name.
            WORDP D = FindWord(word); //   go look up the ~word for it
            if (!D) continue; // topic not found -- shouldnt happen

			// Note- once we have found an initial match for a topic name, we dont want to match that name again...
			// E.g., we have a specific topic for a bot, and later a general one that matches all bots. We dont want that later one processed.
  			if (D->inferMark == inferMark) continue;	// already processed a topic of this name
			D->inferMark = inferMark;

            //   look at references for this topic
            int start = -1;
            while (GetIthSpot(D,++start)) // find matches in sentence
            {
                // value of match of this topic in this sentence
                for ( unsigned int k = positionStart; k <= positionEnd; ++k)
                {
					if (trace & TRACE_PATTERN && CheckTopicTrace()) Log(STDUSERLOG,"%s->%s ",wordStarts[k],word);
                    val += 10 + strlen(wordStarts[k]);   // each hit gets credit 10 and length of word as subcredit
					if (!stricmp(wordStarts[k],word+1) || (wordCanonical[k] && !stricmp(wordCanonical[k],word+1))) val += 20; //  exact hit on topic name
                }
				if (positionEnd < positionStart) // phrase subcomponent
				{
					if (trace & TRACE_PATTERN && CheckTopicTrace())  Log(STDUSERLOG,"%s->%s",wordStarts[positionStart],word);
					val += 10;
  				}
            }

			//   Priority modifiers

			char priority = ' ';
			if (GetTopicFlags(i) & TOPIC_PRIORITY && val)
			{
				priority = '+';
				val  *= 3; //  raise its value
			}
  			else if (GetTopicFlags(i) & TOPIC_LOWPRIORITY && val)
			{
				priority = '-';
				val  /= 3; // lower its value
			}

			topicList[i] = (unsigned short)(val + 1); //  1 means we did compute it, beyond that is value
			if (trace & TRACE_PATTERN && val > 1 && CheckTopicTrace()) Log(STDUSERLOG,"%c(%d) ",priority,topicList[i]);
		} //   close if

        if (val >= max) //  find all best
        {
            if (val > max) // new high value
            {
                max = val;
                index = 0;
            }
            matches[++index] = i;
        }
    }
	if (trace & TRACE_PATTERN && newpass  && CheckTopicTrace()) Log(STDUSERLOG,"\r\n");
	matches[0] = max;
    return index;
}

FunctionResult KeywordTopicsCode(char* buffer)
{	//   find  topics best matching his input words - never FAILS but can return 0 items stored
    unsigned short topicList[MAX_TOPIC_KEYS];
    memset(topicList,0,MAX_TOPIC_KEYS * sizeof(short));
	
	int set = (impliedSet == ALREADY_HANDLED) ? 0 : impliedSet;
	SET_FACTSET_COUNT(set,0);
	
	bool onlyGambits =  (!stricmp(ARGUMENT(1),"gambit")); 

    //   now consider topics in priority order
	SET_FACTSET_COUNT(set,0);
	unsigned int index;
    unsigned int matches[MAX_TOPIC_KEYS];
	NextInferMark();
	while ((index = OrderTopics(topicList,matches))) //   finds all at this level. 1st call evals topics. other calls just retrieve.
    {
        //   see if equally valued topics found are feasible, if so, return one chosen at random
        while (index) // items are 1-based
        {
            unsigned int which = random(index) + 1; 
            unsigned int topic = matches[which];
            topicList[topic] = 1; 
            matches[which] = matches[index--]; // swap equally valued end back to fill in position

			unsigned int flags = GetTopicFlags(topic);
			if (onlyGambits && (flags & TOPIC_SYSTEM || !HasGambits(topic))) continue;
				
			char word[MAX_WORD_SIZE];
			strcpy(word,GetTopicName(topic,true));
			if (impliedSet == ALREADY_HANDLED) // just want one
			{
				strcpy(buffer,word);
				break;
			}

			char value[100];
			sprintf(value,"%d",matches[0]);
			MEANING M = MakeMeaning(StoreWord(word));
			AddFact(set,CreateFact(M,Mkeywordtopics,MakeMeaning(StoreWord(value)),FACTTRANSIENT));
        }   
    }
	if (impliedSet == ALREADY_HANDLED && FACTSET_COUNT(set) == 0) return FAILRULE_BIT;
	impliedSet = ALREADY_HANDLED;
    return NOPROBLEM_BIT;
}

static FunctionResult PendingTopicsCode(char* buffer)
{
	int set = GetSetID(ARGUMENT(1));
	if (set == ILLEGAL_FACTSET) return FAILRULE_BIT;
	PendingTopics(set);
	return NOPROBLEM_BIT;
}

static FunctionResult QueryTopicsCode(char* buffer)
{
	if (impliedSet == ALREADY_HANDLED) // not in assignment
	{
		QueryTopicsOf(ARGUMENT(1),0,NULL); 
		return (FACTSET_COUNT(0)) ? NOPROBLEM_BIT : FAILRULE_BIT;
	}
	return QueryTopicsOf(ARGUMENT(1),impliedSet,NULL); 
}

//////////////////////////////////////////////////////////
/// MARKINGS
//////////////////////////////////////////////////////////

static FunctionResult GetParseCode(char* buffer) 
{  
	char* ptr = ARGUMENT(1); // what
	char* val = ARGUMENT(2); // from where
	
	return FAILRULE_BIT;
}


static FunctionResult MarkCode(char* buffer) 
{  
	// argument1 is a word or ~set or missing entirely
	// mark()  flip off generic unmarks 
	// argument 2 is a location designator or * or missing entirely
	// mark(word) enables mark at location 1 
	// mark(word _xxx) enable word mark at start location of _xxx variable 
	// mark(word  1) enables mark at specified location if within range of input
	// mark(* whatever) turns on any turned off global marking at the range of the given location
	char* ptr = ARGUMENT(1);
	
	FunctionResult result;
	char word[MAX_WORD_SIZE];
	ptr = ReadShortCommandArg(ptr,word,result); // what is being marked
	if (result & ENDCODES) return result;

	if (!*word) // mark() remove all generic unmarks
	{
		if (!oldunmarked[0]) // cache current disables
		{
			memcpy(oldunmarked,unmarked,MAX_SENTENCE_LENGTH);
			oldunmarked[0] = 1;
		}
		memset(unmarked,0,MAX_SENTENCE_LENGTH); // clear all mark suppression
		return NOPROBLEM_BIT;
	}
	
	char word1[MAX_WORD_SIZE];
	if (*ptr == '^')
	{
		ptr = ReadCompiledWord(ptr,word1); // get the request
		size_t len = strlen(callArgumentList[atoi(word1+1)+fnVarBase]);
		if (len >= MAX_WORD_SIZE)  return FAILRULE_BIT;
		strcpy(word1,callArgumentList[atoi(word1+1)+fnVarBase]);
		char word2[MAX_WORD_SIZE];
		if (!IsDigit(*word1) &&  *word1 != '_') 
		{
			strcpy(word2,word1);
			ReadShortCommandArg(word2,word1,result);
		}
	}
	else if (IsDigit(*ptr) || *ptr == '_') ptr = ReadCompiledWord(ptr,word1);  // the locator, leave it unevaled as number or match var
	else ptr = ReadShortCommandArg(ptr,word1,result); // evaluate the locator as a number presumably
	
	unsigned startPosition;
	unsigned endPosition;
	if (!*word1 || *word1 == ')') startPosition = endPosition = 1; // default mark  (ran out or hit end paren of call
	else if (IsDigit(*word1)) endPosition = startPosition = atoi(word1); // named number as index
	else if (*word1 == '_') //  wildcard position designator
	{
		startPosition = wildcardPosition[GetWildcardID(word1)] & 0x0000ffff; // the match location
		endPosition = wildcardPosition[GetWildcardID(word1)] >> 16; 
	}
	else return FAILRULE_BIT;

	if (startPosition < 1) endPosition = startPosition = 1;
	if (startPosition > wordCount)  endPosition = startPosition = wordCount;

	if (*word == '*') // enable all - mark (* _0)
	{
		for (unsigned int i = startPosition; i <= endPosition; ++i) 
		{
			if (showMark) Log(ECHOSTDUSERLOG,"Mark * $d(%s_: \r\n",i,wordStarts[i]);
			if (trace) Log(STDUSERLOG,"mark all @word %s(%d) ",wordStarts[i],i);
			unmarked[i] = 0;
		}
		return NOPROBLEM_BIT;
	}

	// Mark specific thing 
	WORDP D = StoreWord(word);
	MEANING M = MakeMeaning(D);
	if (*D->word != '~') // add ordinary word to concept list directly as WordHit will not store anything but concepts
	{
		unsigned int* entry = (unsigned int*) AllocateString(NULL,2, sizeof(MEANING),false); // ref and link
		entry[1] = concepts[startPosition];
		concepts[startPosition] = String2Index((char*) entry);
		entry[0] = M;
	}
	NextInferMark();
	if (showMark) Log(ECHOSTDUSERLOG,"Mark %s: \r\n",D->word);
	if (trace) Log(STDUSERLOG,"mark all @word %d ",D->word);
	MarkFacts(M,startPosition,endPosition);
	if (showMark) Log(ECHOSTDUSERLOG,"------\r\n");

	return NOPROBLEM_BIT;
}

static FunctionResult MarkedCode(char* buffer)
{
	char* arg1 = ARGUMENT(1);
	if (*ARGUMENT(1) == '$')  // indirect thru variable
	{
		char* at = GetUserVariable(ARGUMENT(1));
		if (at) arg1 = at;
	}

	WORDP D = FindWord(arg1);
	if (!D) return FAILRULE_BIT;
	if (!GetNextSpot(D,0,positionStart,positionEnd)) return FAILRULE_BIT;
	strcpy(buffer,  (char*) "1" );
	return NOPROBLEM_BIT;
}

static FunctionResult PositionCode(char* buffer)
{
	char* ptr = ARGUMENT(1);
	FunctionResult result;
	char word[MAX_WORD_SIZE];
	ptr = ReadShortCommandArg(ptr,word,result); // start or end
	if (result & ENDCODES) return result;
	char word1[MAX_WORD_SIZE];
	ptr = ReadCompiledWord(ptr,word1);  // the _ var
	if (*word1 == '\'') memmove(word1,word1+1,strlen(word1));
	if (*word1 == '^') strcpy(word1,callArgumentList[atoi(word1+1)+fnVarBase]); // swap to actual
	if (*word1 == '_') //  wildcard position designator
	{
		if (!stricmp(word,"start")) sprintf(buffer,"%d",WILDCARD_START(wildcardPosition[GetWildcardID(word1)]));  // the match location
		else if (!stricmp(word,"end")) sprintf(buffer,"%d", WILDCARD_END(wildcardPosition[GetWildcardID(word1)]));
		else if (!stricmp(word,"both")) sprintf(buffer,"%d", wildcardPosition[GetWildcardID(word1)]);
		else return FAILRULE_BIT;
	}
	else return FAILRULE_BIT;
	return NOPROBLEM_BIT;
}

static FunctionResult SetPositionCode(char* buffer)
{
	char* ptr = ARGUMENT(1);
	char word[MAX_WORD_SIZE];

	if (*ptr == '_') // set match var position
	{
		ptr = ReadCompiledWord(ptr,word);
		int n = GetWildcardID(word);
		if (n < 0) return FAILRULE_BIT;

		char startw[MAX_WORD_SIZE];
		FunctionResult result;
		ptr = ReadShortCommandArg(ptr,startw,result); // what is being marked
		if (result != NOPROBLEM_BIT) return result;
		unsigned int start = atoi(startw);
		if (start < 1 || start > wordCount) return FAILRULE_BIT;
		char endw[MAX_WORD_SIZE];
		ptr = ReadShortCommandArg(ptr,endw,result); // what is being marked
		if (result != NOPROBLEM_BIT) return result;
		unsigned int end = atoi(endw);
		if (end < 1 || end > wordCount) return FAILRULE_BIT;
		wildcardPosition[n] = start | (end << 16);
	}
	else
	{
		ptr = ReadArgument(ptr,word);
		unsigned int val = atoi(word);
		if (val == 0) return FAILRULE_BIT;
		positionStart = WILDCARD_START(val);
		if (positionStart > (int)wordCount) positionStart = wordCount;
		unsigned int end = WILDCARD_END(val);
		positionEnd = (end) ? end : positionStart;
	}
	return NOPROBLEM_BIT;
}

static FunctionResult CapitalizedCode(char* buffer)
{
	if (IsDigit(*ARGUMENT(1)))
	{
		unsigned int n = atoi(ARGUMENT(1));
		if (n == 0 || n > wordCount) return FAILRULE_BIT;
		strcpy(buffer,(capState[n]) ? (char*) "1" : (char*) "0");
	}
	else if (IsAlphaUTF8(*ARGUMENT(1))) strcpy(buffer,(IsUpperCase(*ARGUMENT(1))) ? (char*) "1" : (char*) "0");
	else return FAILRULE_BIT;
	return NOPROBLEM_BIT;
}

static FunctionResult RoleCode(char* buffer)
{
	unsigned int n = 0;
	char* arg = ARGUMENT(1);
	if (*arg == '\'') memmove(arg,arg+1,strlen(arg));
	if (IsDigit(*arg))
	{
		unsigned int n = atoi(arg);
		if (n == 0 || n > wordCount) return FAILRULE_BIT;
	}
	else if (*arg == '_') n = WildPosition(arg);
	else if (*arg == '$') n = atoi(GetUserVariable(arg));
	else if (*arg == '^') 
	{
		char word[MAX_WORD_SIZE];
		ReadArgument(arg,word);
		n = atoi(word);
	}
	else return FAILRULE_BIT;
	sprintf(buffer,"%u", (unsigned int)roles[n]);
	return NOPROBLEM_BIT;
}

static FunctionResult DecodePosCode(char* buffer)
{
	char* arg1 = ARGUMENT(1);
	char* arg = ARGUMENT(2);
	int64 n;
	ReadInt64(arg,n);
	if (!stricmp(arg1,"pos")) DecodeTag(buffer,n, 0,0);
	else strcpy(buffer,GetRole(n));
	return NOPROBLEM_BIT;
}

static FunctionResult PartOfSpeechCode(char* buffer)
{
	unsigned int n = 0;
	char* arg = ARGUMENT(1);
	if (*arg == '\'') memmove(arg,arg+1,strlen(arg));
	if (IsDigit(*arg))
	{
		unsigned int n = atoi(arg);
		if (n == 0 || n > wordCount) return FAILRULE_BIT;
		strcpy(buffer,(capState[n]) ? (char*) "1" : (char*) "0");
	}
	else if (*arg == '_')  n = WildPosition(arg);
	else if (*arg == '^') 
	{
		char word[MAX_WORD_SIZE];
		ReadArgument(arg,word);
		n = atoi(word);
	}
	else if (*arg == '$') n = atoi(GetUserVariable(arg));
	else return FAILRULE_BIT;
	uint64 pos = finalPosValues[n];
	if (pos & (AUX_VERB | ADJECTIVE_PARTICIPLE )) pos |= allOriginalWordBits[n] & VERB_BITS; // supllementatal data
	else if (pos &  ADJECTIVE_NORMAL && allOriginalWordBits[n] & ADJECTIVE_PARTICIPLE) pos |= allOriginalWordBits[n] & VERB_BITS; // supllementatal data
	else if (pos & ADJECTIVE_NOUN) pos |= allOriginalWordBits[n] & NORMAL_NOUN_BITS;

#ifdef WIN32
	sprintf(buffer,"%I64d",pos); 
#else
	sprintf(buffer,"%lld",pos); 
#endif
	return NOPROBLEM_BIT;
}

static FunctionResult KeepHistoryCode(char* buffer)
{
	unsigned int count = atoi(ARGUMENT(2));
	if (count >= (MAX_USED - 1)) count = MAX_USED - 1; 
	if (!stricmp(ARGUMENT(1),"BOT"))
	{
		if (count == 0) *chatbotSaid[0] = 0;
		if (count < chatbotSaidIndex)  chatbotSaidIndex = count;
	}
	if (!stricmp(ARGUMENT(1),"USER"))
	{
		if (count == 0)  *humanSaid[0] = 0;
		if (count < humanSaidIndex) humanSaidIndex = count;
	}

	return NOPROBLEM_BIT;
}

static FunctionResult UnmarkCode(char* buffer)
{
	// unmark() // disable global unmarks
	// unmark(*) // global unmark all words individually
	// unmark(* 4)	 // global unmark this location
	// unmark(* _location) // global unmark range
	// unmark(word 4)
	// unmark(word _location)
	// unmark(word all)

	char* ptr = ARGUMENT(1);
	char word[MAX_WORD_SIZE];
	FunctionResult result;
	ptr = ReadShortCommandArg(ptr,word,result);// set
	if (result & ENDCODES) return result;
	if (matching) clearUnmarks = true;
	
	if (!*word) // unmark() reenables generic unmarking
	{
		if (oldunmarked[0]) // merge state back if have cached
		{
			memcpy(unmarked,oldunmarked,MAX_SENTENCE_LENGTH);
			oldunmarked[0] = 0;
		}
		return NOPROBLEM_BIT;
	}
	
	// get location
	char word1[MAX_WORD_SIZE];
	ptr = ReadCompiledWord(ptr,word1);  // the _data
	unsigned int startPosition = wordCount;
	unsigned int endPosition = 1;
	if (!*word1) 
	{
		if (*word == '*') // unmark(*)
		{
			startPosition = startSentence;
			endPosition = endSentence;
		}
		else startPosition = endPosition = 1;
	}
	else if (IsDigit(*word1)) startPosition = endPosition = atoi(word1);
	else if (*word1 == '_') 
	{
		startPosition = WILDCARD_START(wildcardPosition[GetWildcardID(word1)]); // the match location
		endPosition = WILDCARD_END(wildcardPosition[GetWildcardID(word1)]);
	}
	else if (!stricmp(word1,"all")) // remove ALL references anywhere of this
	{
		WORDP D = FindWord(word); //   set or word to unmark
		if (!D) return FAILRULE_BIT;
		D->temps = 0; 
		return NOPROBLEM_BIT;
	}
 	else  return FAILRULE_BIT;
	if (!startPosition || startPosition > wordCount) return NOPROBLEM_BIT;	// fail silently
	if (*word == '*') // set unmark EVERYTHING in range 
	{
		unmarked[startPosition] = 1;
		if (trace) Log(STDUSERLOG,"unmark all = (%d %s) ",startPosition,wordStarts[startPosition]);
		for (unsigned int i = startPosition+1; i <= endPosition; ++i) 
		{
			if (trace) Log(STDUSERLOG,"unmark=(%d %s) ",i,wordStarts[i]);
			unmarked[i] = 1;
		}
	}
	else
	{
		WORDP D = FindWord(word); //   set or word to unmark at specific location
		if (D) RemoveMatchValue(D,startPosition);
	}
	return NOPROBLEM_BIT;
}

//////////////////////////////////////////////////////////
/// INPUT ROUTINES
//////////////////////////////////////////////////////////

static FunctionResult InputCode(char* buffer) 
{      // when supplying multiple sentences, must do them in last first order
	if (inputCounter++ > 5) return FAILRULE_BIT;// limit per sentence reply
	if (totalCounter++ > 15) return FAILRULE_BIT; // limit per input from user

	if (trace & TRACE_OUTPUT && CheckTopicTrace()) Log(STDUSERLOG,"\r\n");
	FunctionResult result;
	char* word = ARGUMENT(1);
	Output(word,buffer,result);
	if (strlen(buffer) >= INPUT_BUFFER_SIZE) buffer[INPUT_BUFFER_SIZE-1] = 0;	// might be smaller buffer
	Convert2Blanks(buffer); // break apart underscored words
	if (!strcmp(lastInputSubstitution,buffer)) return FAILRULE_BIT; // same result as before, apparently looping

	if (showInput)
	{
		bool oldecho = echo;
		echo = true;
		Log(STDUSERLOG,"^input: %s\r\n",buffer);
		echo = oldecho;
	}
	else if (trace) Log(STDUSERLOG,"^input given: %s\r\n",buffer);
	AddInput(buffer);
	strcpy(lastInputSubstitution,buffer);
    *buffer = 0;
	return NOPROBLEM_BIT;
}

static FunctionResult RemoveTokenFlagsCode(char* buffer)
{
	int64 flags;
	ReadInt64(ARGUMENT(1),flags);
	tokenFlags &= -1 ^ flags;
	return NOPROBLEM_BIT;
}

static FunctionResult SetTokenFlagsCode(char* buffer)
{
	int64 flags;
	ReadInt64(ARGUMENT(1),flags);
	tokenFlags |= flags;
	return NOPROBLEM_BIT;
}

static FunctionResult SetWildcardIndexCode(char* buffer)
{
	char* arg1 = ARGUMENT(1);
	int index = GetWildcardID(arg1);
	if (index < 0) return FAILRULE_BIT;
	SetWildCardIndexStart(index); // start here
	return NOPROBLEM_BIT;
}

//////////////////////////////////////////////////////////
/// NUMBER FUNCTIONS
//////////////////////////////////////////////////////////

static FunctionResult ComputeCode(char* buffer)
{
	int64 value = NOT_A_NUMBER;
	char* arg1 = ARGUMENT(1);
	char* op = ARGUMENT(2);
	char* arg2 = ARGUMENT(3);
	//   for long digits, move to float
	if (strlen(arg2) >= 11 || strlen(arg1) >= 11 || strchr(arg1,'.') || strchr(arg2,'.') || !stricmp(op,"divide") || !stricmp(op,"root") || !stricmp(op,"square_root") || !stricmp(op,"quotient") || *op == '/') //   float
	{
		float value = (float) NOT_A_NUMBER;
		float number1 = (strchr(arg1,'.')) ? (float) atof(arg1) : (float)Convert2Integer(arg1);
		float number2 = (strchr(arg2,'.')) ? (float) atof(arg2) :  (float)Convert2Integer(arg2);
		//   we must test case insenstive because arg2 might be capitalized (like add and ADD for attention deficit disorder)
		if (*op == '+' || !stricmp(op,"plus") || !stricmp(op,"add")|| !stricmp(op,"and")) value = number1 + number2; 
		else if (!stricmp(op,"minus") || !stricmp(op,"subtract")|| !stricmp(op,"deduct")|| !stricmp(op,"take away") || *op == '-' ) value = number1 - number2;
		else if (!stricmp(op,"x") || !strnicmp(op,"times",4) || !stricmp(op,"multiply") || *op == '*') value = number1 * number2;
		else if (!stricmp(op,"divide") || !stricmp(op,"quotient") || *op == '/' ) 
		{
			if (number2 == 0) 
			{
				strcpy(buffer,"infinity");
				return NOPROBLEM_BIT;
			}
			else value = number1 / number2;
		}
        else if (!stricmp(op,"remainder") || !stricmp(op,"modulo") || !stricmp(op,"mod") || *op == '%') 
		{
			ReportBug("illegal mod op in float")
			return FAILRULE_BIT;
		}
        else if (!stricmp(op,"random") )
		{
			ReportBug("illegal random op in float")
  			return FAILRULE_BIT;
		}
        else if (!stricmp(op,"root") || !stricmp(op,"square_root") ) value = (float) sqrt(number1);  
        else if (!stricmp(op,"^") || !stricmp(op,"^^") ||!stricmp(op,"power") || !stricmp(op,"exponent")) 
        {
			int power = (int)Convert2Integer(arg2);
            if (power >= 1 && power <= 10)
            {
				value = number1;
				while (--power) value *= number1;
			}
            else if (power == 0) value = 1;
		}
		if (value != NOT_A_NUMBER) 
		{
			int x = (int) value;
			strcpy(buffer,((float)x == value) ? StdIntOutput(x) : StdFloatOutput(value));
		}
		else sprintf(buffer," ?");
	}
	else //   integer
    {
		int64 value1 = Convert2Integer(arg1);
		int64 value2 = Convert2Integer(arg2);
		if (*op == '+' || !stricmp(op,"add")|| !stricmp(op,"and") || !stricmp(op,"plus")) value = value1 + value2;
		else if (*op == '-' || !stricmp(op,"deduct") || !stricmp(op,"minus") || !stricmp(op,"sub") || !stricmp(op,"subtract") || !stricmp(op,"take_away")) value = value1 - value2;
		else if (*op == '*' || !stricmp(op,"x") || !stricmp(op,"multiply") || !strnicmp(op,"times",4)) value = value1 * value2;
		else if ( *op == '%' || !stricmp(op,"mod") || !strcmp(op,"modulo") || !stricmp(op,"remainder")) value = value1 % value2;
		else if (!stricmp(op,"random")) value = random((unsigned int)(value2 - value1)) + value1; 
 		else if (*op == '<' && op[1] == '<')  value = value1 << value2;  // BUT FLAWED if shift >= 32
		else if (*op == '>' && op[1] == '>') value = value1 >> value2;
		else if (*op == '^' || !stricmp(op,"exponent") || !stricmp(op,"power"))
		{
			if (value2 >= 1 && value2 <= 10) // only do small powers
			{
				value = value1;
				while (--value2) value *= value1;
			}
			else if (value2 == 0) value = 1;
		}
        strcpy(buffer, (value == NOT_A_NUMBER) ? (char*)"?" : StdIntOutput((int)value));
	}
	return NOPROBLEM_BIT;
}

static FunctionResult IsNumberCode(char* buffer)
{
	return IsDigitWord(ARGUMENT(1)) ? NOPROBLEM_BIT : FAILRULE_BIT;
}

static FunctionResult TimeFromSecondsCode(char* buffer)
{
	int64 seconds;
	char* word = ARGUMENT(1);
	ReadInt64(word,seconds);
	time_t sec = (time_t) seconds;
	
	// convert to text string
	strcpy(buffer,ctime(&sec));
	*strchr(buffer,'\n') = 0; // erase newline at end

	return NOPROBLEM_BIT;
}

static FunctionResult TimeInfoFromSecondsCode(char* buffer)
{
	int64 seconds;
	char* word = ARGUMENT(1);
	ReadInt64(word,seconds);
	time_t sec = (time_t) seconds;
	struct tm *time = localtime((time_t *)&seconds);
	if (impliedWild != ALREADY_HANDLED)  
	{
		SetWildCardIndexStart(impliedWild); //   start of wildcards to spawn
		impliedWild = ALREADY_HANDLED;
	}
	else SetWildCardIndexStart(0); //   start of wildcards to spawn
	char value[MAX_WORD_SIZE];
	sprintf(value,"%d",time->tm_sec);
	SetWildCard(value,value,0,0);
	sprintf(value,"%d",time->tm_min);
	SetWildCard(value,value,0,0);
	sprintf(value,"%d",time->tm_hour);
	SetWildCard(value,value,0,0);
	sprintf(value,"%d",time->tm_mday);
	SetWildCard(value,value,0,0);
	sprintf(value,"%s",months[time->tm_mon]); // january = 0
	SetWildCard(value,value,0,0);
	sprintf(value,"%d",time->tm_year + 1900);
	SetWildCard(value,value,0,0);
	sprintf(value,"%s",days[time->tm_wday]); // sunday = 0
	SetWildCard(value,value,0,0);

	return NOPROBLEM_BIT;
}


static FunctionResult TimeToSecondsCode(char* buffer)
{
	struct tm timeinfo;
	time_t rawtime;
	time (&rawtime );
	memcpy((char*)&timeinfo,(char*)localtime (&rawtime ),sizeof(timeinfo)); // get daylight savings value in

	char* x = GetTimeInfo();
	/*
	tm_sec	int	seconds after the minute	0-61*
	tm_min	int	minutes after the hour	0-59
	tm_hour	int	hours since midnight	0-23
	tm_mday	int	day of the month	1-31
	tm_mon	int	months since January	0-11
	tm_year	int	years since 1900	
	tm_wday	int	days since Sunday	0-6
	tm_yday	int	days since January 1	0-365
	tm_isdst	int	Daylight Saving Time flag	
	*/
	//   Www Mmm dd hh:mm:ss yyyy Where Www is the weekday, Mmm the month in letters, dd the day of the month, hh:mm:ss the time, and yyyy the year. Sat May 20 15:21:51 2000
	timeinfo.tm_wday = timeinfo.tm_yday = 0;
	char* seconds = ARGUMENT(1);  
	if (*seconds == '-') return FAILRULE_BIT;
	ReadInt(seconds,*(unsigned int*)&timeinfo.tm_sec);
	if (timeinfo.tm_sec > 61) return FAILRULE_BIT; // leap seconds allowed
	char* minutes = ARGUMENT(2);  
	if (*minutes == '-') return FAILRULE_BIT;
	timeinfo.tm_min = atoi(minutes);
	char* hours = ARGUMENT(3);  
	if (*hours == '-') return FAILRULE_BIT;
	timeinfo.tm_hour = atoi(hours);
	char* day = ARGUMENT(4);  
	if (!IsDigit(*day)) return FAILRULE_BIT;
	timeinfo.tm_mday = atoi(day);
	if (timeinfo.tm_mday == 0) return FAILRULE_BIT; // day must be 1 or higher

	char* month = ARGUMENT(5);  
	if (IsDigit(*month)) timeinfo.tm_mon = atoi(month) - 1;	 // 0 based
	else if (!strnicmp(month,"jan",3)) timeinfo.tm_mon = 0;
	else if (!strnicmp(month,"feb",3)) timeinfo.tm_mon = 1;
	else if (!strnicmp(month,"mar",3)) timeinfo.tm_mon = 2;
	else if (!strnicmp(month,"apr",3)) timeinfo.tm_mon = 3;
	else if (!strnicmp(month,"may",3)) timeinfo.tm_mon = 4;
	else if (!strnicmp(month,"jun",3)) timeinfo.tm_mon = 5;
	else if (!strnicmp(month,"jul",3)) timeinfo.tm_mon = 6;
	else if (!strnicmp(month,"aug",3)) timeinfo.tm_mon = 7;
	else if (!strnicmp(month,"sep",3)) timeinfo.tm_mon = 8;
	else if (!strnicmp(month,"oct",3)) timeinfo.tm_mon = 9;
	else if (!strnicmp(month,"nov",3)) timeinfo.tm_mon = 10;
	else if (!strnicmp(month,"dec",3)) timeinfo.tm_mon = 11;
	char* year = ARGUMENT(6);  
	if (*year == '-') return FAILRULE_BIT;
	timeinfo.tm_year = atoi(year); // years since 1900
	if (timeinfo.tm_year < 1970 || timeinfo.tm_year > 2100) return FAILRULE_BIT; // unacceptable year
	timeinfo.tm_year -= 1900;	// pass in as years since 1900
	char* daylightsavings = ARGUMENT(7);  
	if (*daylightsavings == '1' || *daylightsavings == 't' ||  *daylightsavings == 'T') timeinfo.tm_isdst = 1;
	else if (*daylightsavings == '0' || *daylightsavings == 'f' ||  *daylightsavings == 'F') timeinfo.tm_isdst = 0;
	
	time_t time = mktime (&timeinfo);
	if (time == -1) return FAILRULE_BIT;
#ifdef WIN32
    sprintf(buffer,"%I64d",time); 
#else
	sprintf(buffer,"%lld",time);
#endif
	return NOPROBLEM_BIT;
}
//////////////////////////////////////////////////////////
/// DEBUG FUNCTIONS
//////////////////////////////////////////////////////////

static FunctionResult LogCode(char* buffer)
{
	char* stream = ARGUMENT(1);
	uint64 flags;
	bool bad = false;
	stream = ReadFlags(stream,flags,bad); // try for flags
	if (flags && *stream == ')') ++stream; // skip end of flags
	char name[MAX_WORD_SIZE];
	*name = 0;
	FunctionResult result;
	bool keep = false;
	char* fname =  NULL;
	if (!strnicmp(stream,"CLOSE",5))
	{
		stream = ReadCompiledWord(stream,name); // close
		stream = ReadCommandArg(stream,name,result,OUTPUT_NOQUOTES|OUTPUT_EVALCODE|OUTPUT_NOTREALBUFFER); // name of file
		if (*name == '"') 
		{
			size_t len = strlen(name);
			name[len-1] = 0;	// remove trailing "
		}
		fname = (*name == '"') ? (name+1) : name;
		for (unsigned int i = 0; i <= MAX_LOG_NAMES; ++i)
		{
			if (!stricmp(fname,lognames[i])) // found already open
			{
				fclose(logfiles[i]);
				logfiles[i] = NULL;
				*lognames[i] = 0;
				return NOPROBLEM_BIT;
			}
		}
		return FAILRULE_BIT;
	}

	if (!strnicmp(stream,"OPEN ",4)) keep = true; // dont close it
	if (!strnicmp(stream,"FILE ",5) || !strnicmp(stream,"OPEN ",4)) // write data to this file
	{
		stream = ReadCompiledWord(stream,name); // FILE or OPEN
		stream = ReadCommandArg(stream,name,result,OUTPUT_NOQUOTES|OUTPUT_EVALCODE|OUTPUT_NOTREALBUFFER); // name of file
		if (*name == '"') 
		{
			size_t len = strlen(name);
			name[len-1] = 0;	// remove trailing "
		}
		fname = (*name == '"') ? (name+1) : name;
		if (!strnicmp(stream,"NEW",3)) // start with a clean file
		{
			char junk[MAX_WORD_SIZE];
			stream = ReadCompiledWord(stream,junk);
			FILE* out = FopenUTF8Write(fname);
			if (out) fclose(out);
			else return FAILRULE_BIT;
		}
	}

	++outputNest;
	WORDP lock = dictionaryLocked;
	dictionaryLocked = (WORDP)22; // allow format string to work even while compiling a table
	Output(stream,buffer,result,OUTPUT_EVALCODE | (unsigned int) flags | OUTPUT_NOTREALBUFFER);
	--outputNest;
	dictionaryLocked = lock;

	if (fname)
	{
		FILE* out = NULL;
		bool cached = false;
		for (unsigned int i = 0; i <= MAX_LOG_NAMES; ++i)
		{
			if (!stricmp(fname,lognames[i])) // found already open
			{
				out = logfiles[i]; 
				cached = true;
				break;
			}
		}
		if (!out) // not cached
		{
			out = FopenUTF8WriteAppend(fname);
			if (keep)
			{
				for (unsigned int i = 0; i <= MAX_LOG_NAMES; ++i) // try to cache it
				{
					if (!logfiles[i]) // found already open
					{
						logfiles[i] = out; 
						strcpy(lognames[i],fname);
						cached = true;
						break;
					}
				}
			}
		}
		if (out) 
		{
			fwrite(buffer,1,strlen(buffer),out);
			if (!cached) fclose(out);
		}
		else 
		{
			*buffer = 0;
			return FAILRULE_BIT;
		}
	}
	else Log(STDUSERLOG,"%s",buffer);
	if (flags & OUTPUT_ECHO && !echo) printf("%s",buffer);
	*buffer = 0;
	return NOPROBLEM_BIT;
}


//////////////////////////////////////////////////////////
/// OUTPUT FUNCTIONS
//////////////////////////////////////////////////////////

static FunctionResult FlushOutputCode(char* buffer)
{
	if (planning) return FAILRULE_BIT;
	if (postProcessing)
	{
		ReportBug("Illegal to use ^FlushOutput during postprocessing");
		return FAILRULE_BIT;
	}
	if (!AddResponse(currentOutputBase)) return FAILRULE_BIT;
	return NOPROBLEM_BIT;
}

static FunctionResult InsertOutput(char* stream, char* buffer, int index)
{
	// add at end, then alter order
	FunctionResult result;
	Output(stream,buffer,result,OUTPUT_EVALCODE);
	if (AddResponse(buffer))
	{
		memmove(&responseOrder[index+1],&responseOrder[index],responseIndex - index); // shift order out 1
		responseOrder[index] = (unsigned char)(responseIndex-1);
	}
	else result = FAILRULE_BIT;
	return result;
}

static FunctionResult InsertPrintCode(char* buffer) 
{     
	if (planning) return FAILRULE_BIT;
	if (postProcessing)
	{
		ReportBug("Illegal to use ^InsertPrePrint during postprocessing");
		return FAILRULE_BIT;
	}
	char* stream = ARGUMENT(1);
	uint64 flags;
	bool bad = false;
	stream = ReadFlags(stream,flags,bad); // try for flags
	if (flags) ++stream; // skip end of flags
	FunctionResult result;
	char beforeIndex[MAX_WORD_SIZE];
	stream = ReadShortCommandArg(stream,beforeIndex,result); 
	int index = 0;
	
	if (*beforeIndex == '~') // put before 1st reference to this topic
	{
		unsigned int topic = FindTopicIDByName(beforeIndex);
		for (int i = responseIndex-1; i > 0; --i)
		{
			if (topic == responseData[responseOrder[i]].topic) index = responseOrder[i];
		}	
	}
	else if (IsDigit(*beforeIndex)) // numeric index he gives must be 1 based, eg before %response 
	{
		index = atoi(beforeIndex);
		if (index <= 0 || index > (int)responseIndex) return FAILRULE_BIT;
		index = responseOrder[index-1]; // the current location of the output
	}
	return InsertOutput(stream,buffer,index);
}

static FunctionResult PrintCode(char* buffer) 
{     
	if (planning) return FAILRULE_BIT;
	if (postProcessing)
	{
		ReportBug("Illegal to use ^Print during postprocessing");
		return FAILRULE_BIT;
	}
	char* stream = ARGUMENT(1);
	uint64 flags;
	bool bad = false;
	stream = ReadFlags(stream,flags,bad); // try for flags
	if (flags && *stream == ')') ++stream; // skip end of flags

	FunctionResult result;
	Output(stream,buffer,result,OUTPUT_EVALCODE | (unsigned int) flags);
	if (!AddResponse(buffer)) result = FAILRULE_BIT;
	return result;
}

static FunctionResult PrePrintCode(char* buffer)
{
	if (planning) return FAILRULE_BIT;
	if (postProcessing)
	{
		ReportBug("Illegal to use ^PrePrint during postprocessing");
		return FAILRULE_BIT;
	}
	char* stream = ARGUMENT(1); 
	uint64 flags;
	bool bad = false;
	stream = ReadFlags(stream,flags,bad); // try for flags
	if (flags) ++stream; // skip end of flags

	return InsertOutput(stream,buffer,0);
}

static FunctionResult RepeatCode(char* buffer)
{ 
	if (postProcessing)
	{
		ReportBug("Illegal to use ^Repeat during postprocessing");
		return FAILRULE_BIT;
	}
	AddRepeatable(currentRule); // local repeats allowed this volley
	return NOPROBLEM_BIT;
}

static FunctionResult SetPronounCode(char* buffer) 
{  
	// argument1 is a word to use
	// mark(word _xxx) enable word mark at location of _xxx variable
	char* ptr = ARGUMENT(1);
	if (!*ptr) return FAILRULE_BIT;

	FunctionResult result;
	char word[MAX_WORD_SIZE];
	ptr = ReadShortCommandArg(ptr,word,result); // what is being marked
	if (result & ENDCODES) return result;
	if (!*word) return FAILRULE_BIT; // missing arg

	char word1[MAX_WORD_SIZE];
	ptr = ReadCompiledWord(ptr,word1);  // the locator

	unsigned startPosition;
	unsigned endPosition;
	if (!*word1 || *word1 == ')') startPosition = endPosition = 1; // default mark  (ran out or hit end paren of call
	else if (IsDigit(*word1)) endPosition = startPosition = atoi(word1); // named number as index
	else if (*word1 == '_') //  wildcard position designator
	{
		startPosition = wildcardPosition[GetWildcardID(word1)] & 0x0000ffff; // the match location
		endPosition = wildcardPosition[GetWildcardID(word1)] >> 16; 
	}
	else return FAILRULE_BIT;

	if (startPosition < 1) startPosition = 1;
	if (startPosition > wordCount)  startPosition = wordCount;
	WORDP D = StoreWord(word);
	MarkFacts(MakeMeaning(D),startPosition,startPosition);

	WORDP entry;
	WORDP canonical;
	uint64 sysflags = 0;
	uint64 cansysflags = 0;
	GetPosData(2,word,entry,canonical,sysflags,cansysflags,false); // NOT first try
	wordStarts[startPosition] = D->word; 
	wordCanonical[startPosition] = (canonical) ? canonical->word : D->word;	
	if (!wordCanonical[startPosition]) wordCanonical[startPosition] = D->word;

	uint64 bits = D->properties & (NOUN_PROPERTIES | NOUN_BITS|NOUN_INFINITIVE|LOWERCASE_TITLE);
	allOriginalWordBits[startPosition] = bits;
	finalPosValues[startPosition] = bits;
	MarkTags(startPosition);

	return NOPROBLEM_BIT;
}

//////////////////////////////////////////////////
/// OUTPUT ACCESS
//////////////////////////////////////////////////

static FunctionResult LastSaidCode(char* buffer)
{
	if (chatbotSaidIndex) 
	{
		sprintf(buffer,"%s",chatbotSaid[chatbotSaidIndex-1]);
		char* special;
		char* at = buffer;
		while ((special = strchr(at,'\\')))
		{
			if (special[1] == 'r')
			{
				memmove(special+1,special+2,strlen(special+1));
				*special = '\r';
			}
			else if (special[1] == 'n')
			{
				memmove(special+1,special+2,strlen(special+1));
				*special = '\n';
			}
			at = special+1;
		}
	}
	return NOPROBLEM_BIT;
}

static FunctionResult ResponseCode(char* buffer)
{
	unsigned int index = atoi(ARGUMENT(1)) ;
	if (index > responseIndex || !index) return FAILRULE_BIT;
	sprintf(buffer,"%s",responseData[responseOrder[index-1]].response);
	return NOPROBLEM_BIT;
}

static FunctionResult ResponseQuestionCode(char* buffer)
{
	unsigned int index = atoi(ARGUMENT(1)) - 1; // which response (1 based)
	if (index >= responseIndex) return FAILRULE_BIT;
	char* ptr = TrimSpaces(responseData[responseOrder[index]].response,false);
	strcpy(buffer,(ptr[strlen(ptr)-1] == '?') ? (char*) "1" : (char*) ""); 
	return NOPROBLEM_BIT;
}

static FunctionResult ResponseRuleIDCode(char* buffer)
{
	unsigned int index = atoi(ARGUMENT(1));
	if (index > responseIndex || !index) return FAILRULE_BIT;
	int topic = responseData[responseOrder[index-1]].topic;
	sprintf(buffer,"%s%s",GetTopicName(topic),responseData[responseOrder[index-1]].id);
	return NOPROBLEM_BIT;
}

//////////////////////////////////////////////////////////
/// POSTPROCESSING FUNCTIONS
//////////////////////////////////////////////////////////

static FunctionResult AnalyzeCode(char* buffer)
{
	char* word = ARGUMENT(1);
	SAVEOLDCONTEXT()
	FunctionResult result;
	Output(word,buffer,result);
	Convert2Blanks(buffer); // remove any system underscoring back to blanks
	if (*buffer == '"') // if a string, remove quotes
	{
		size_t len = strlen(buffer);
		if (buffer[len-1] == '"') 
		{
			buffer[len-1] = 0;
			*buffer = ' ';
		}
	}
	PrepareSentence(buffer,true,false); 
	*buffer = 0; // only wanted effect of script
	RESTOREOLDCONTEXT()
	return NOPROBLEM_BIT;
}

static FunctionResult PostPrintBeforeCode(char* buffer) // only works if post processing
{     
	if (!postProcessing) 
	{
		ReportBug("Cannot use ^PostPrintBefore except in postprocessing");
		return FAILRULE_BIT;
	}
	
	char* stream = ARGUMENT(1);		
	uint64 flags;
	bool bad = false;
	stream = ReadFlags(stream,flags,bad); // try for flags
	if (flags) ++stream; // skip end of flags

	FunctionResult result;
	Output(stream,buffer,result,OUTPUT_EVALCODE| (unsigned int)flags);

	// prepend output 
	strcat(buffer," ");
	strcat(buffer,postProcessing);
	strcpy(postProcessing,buffer);
	*buffer = 0;
	return result;
}

static FunctionResult PostPrintAfterCode(char* buffer) // only works if post processing
{     
	if (!postProcessing) 
	{
		ReportBug("Cannot use ^PostProcessPrintAfter except in postprocessing");
		return FAILRULE_BIT;
	}
	
	char* stream = ARGUMENT(1);		
	uint64 flags;
	bool bad = false;
	stream = ReadFlags(stream,flags,bad); // try for flags
	if (flags) ++stream; // skip end of flags

	FunctionResult result;
	Output(stream,buffer,result,OUTPUT_EVALCODE| (unsigned int)flags);

	// postpend output 
	size_t len = strlen(postProcessing);
	char* end = postProcessing + len;
	if (len > 0) *end++ = ENDUNIT; // add separating item from last unit for log detection
	strcpy(end,buffer);
	*buffer = 0;
	return result;
}

static FunctionResult ReviseOutputCode(char* buffer)
{
	if (postProcessing) return FAILRULE_BIT;
	char* arg1 = ARGUMENT(1); // index first, rest is output
	unsigned int index = atoi(arg1);
	if (!IsDigit(*arg1)) return FAILRULE_BIT;
	if (index > responseIndex) return FAILRULE_BIT;
	char* arg2 = ARGUMENT(2);
	strcpy(responseData[index-1].response,arg2);
	return NOPROBLEM_BIT;
}

//////////////////////////////////////////////////////////
/// COMMAND FUNCTIONS
//////////////////////////////////////////////////////////

static FunctionResult CommandCode(char* buffer) 
{
	DoCommand(ARGUMENT(1),NULL,false);
	return NOPROBLEM_BIT;
}

FunctionResult IdentifyCode(char* buffer) 
{	
	char* os;
#ifdef WIN32
	os = "Windows";
#elif IOS
	os = "IOS";
#elif __MACH__
	os = "MACH";
#else
	os = "LINUX";
#endif
	sprintf(buffer,"ChatScript Version %s  %ld bit %s compiled %s\r\n",version,(long int)(sizeof(char*) * 8),os,compileDate);

	return NOPROBLEM_BIT;
}

FunctionResult DebugCode(char* buffer) 
{	
	char* xarg = ARGUMENT(1);
	if (!stricmp(xarg,"deeptrace") && trace) deeptrace = !deeptrace;
	return NOPROBLEM_BIT;
}

static FunctionResult EndCode(char* buffer)
{ 
	char* word = ARGUMENT(1);
	if (!stricmp(word,"RULE")) return ENDRULE_BIT;
	if (!stricmp(word,"LOOP")) return ENDLOOP_BIT;
	if (!stricmp(word,"TOPIC") || !stricmp(word,"PLAN")) return ENDTOPIC_BIT;
	if (!stricmp(word,"SENTENCE")) return ENDSENTENCE_BIT;
	if (!stricmp(word,"INPUT")) return ENDINPUT_BIT;
  	if (!stricmp(word,"CALL")) return ENDCALL_BIT;
	return FAILRULE_BIT;
}

static FunctionResult EvalCode(char* buffer) //  ??? needed with output eval instead?
{	
	FunctionResult result;
	char* stream = ARGUMENT(1);
	uint64 flags;
	bool bad = false;
	stream = ReadFlags(stream,flags,bad); // try for flags
	if (flags && *stream == ')') ++stream; // skip end of flags
	Output(stream,buffer,result,OUTPUT_EVALCODE|(unsigned int)flags); 
	return result;
}

static FunctionResult FailCode(char* buffer) 
{      
	char* word = ARGUMENT(1);
	if (!stricmp(word,"LOOP")) return FAILRULE_BIT;
	if (!stricmp(word,"RULE")) return FAILRULE_BIT;
	if (!stricmp(word,"TOPIC") || !stricmp(word,"PLAN")) 
	{
		RemovePendingTopic(currentTopicID);
		return FAILTOPIC_BIT;
	}
	if (!stricmp(word,"SENTENCE")) return FAILSENTENCE_BIT;
	if (!stricmp(word,"INPUT")) return FAILINPUT_BIT;
	return FAILRULE_BIT;
}

FunctionResult MatchCode(char* buffer) 
{     
	char word[MAX_WORD_SIZE];
	char word1[MAX_WORD_SIZE];
	char* at = ReadCompiledWord(ARGUMENT(1),word1);
	if (*word1 == '$' && !*at) strcpy(word,GetUserVariable(word1)); //   solitary user var, decode it  eg match($var)
	else if (*word1 == '_' && !*at) strcpy(word,wildcardCanonicalText[GetWildcardID(word1)]); //   solitary user var, decode it  eg match($var)
	else 
	{
		if (word1[0] == FUNCTIONSTRING && word1[1] == '(') strcpy(word,word1+1);
		else strcpy(word,word1); // otherwise it is what to say (like from idiom table)
		Convert2Blanks(word);
	}
	char* ptr = word;
	if (*word)  
	{
		size_t len = strlen(word);
		strcpy(word+len," )"); // insure it has a closing paren (even if it has);
		if (*word == '"') 
		{
			word[len-1] = ' '; // change closing " to space
			++ptr;	// skip opening "
			if (*ptr == FUNCTIONSTRING) ++ptr; // bypass the mark

			// now purify of any internal \" " marked strings
			char* x = strchr(ptr,'\\');
			while (x)
			{
				if (x[1] == '"') memmove(x,x+1,strlen(x));	// remove escape
				x = strchr(x + 1,'\\'); // next?
			}
		}
	}
	if (*ptr == FUNCTIONSTRING) ++ptr;	// skip compiled string mark
	if (*ptr == '(') ++ptr;		// skip opening paren of a pattern
	while (*ptr == ' ') ++ptr;	// prepare for start
	unsigned int gap = 0;
	unsigned int wildcardSelector = 0;
	wildcardIndex = 0;  //   reset wildcard allocation on top-level pattern match
	unsigned int junk;
	if (!*word) return FAILRULE_BIT;	// NO DATA?
	bool uppercasem = false;
	int matched = 0;
    bool match = Match(ptr,0,0,'(',true,gap,wildcardSelector,junk,junk,uppercasem,matched) != 0;  //   skip paren and treat as NOT at start depth, dont reset wildcards- if it does match, wildcards are bound
	if (!match) return FAILRULE_BIT;
	return NOPROBLEM_BIT;
}

static FunctionResult NoFailCode(char* buffer)
{      
	char word[MAX_WORD_SIZE];
	char* ptr = ReadCompiledWord(ARGUMENT(1),word);
	FunctionResult result;
	ChangeDepth(1,"noFailCode");
	Output(ptr,buffer,result);
	ChangeDepth(-1,"noFailCode");
	if (!stricmp(word,"RULE")) return (FunctionResult) (result & (ENDTOPIC_BIT|FAILTOPIC_BIT|RETRYTOPIC_BIT|ENDSENTENCE_BIT|FAILSENTENCE_BIT|ENDINPUT_BIT|RETRYSENTENCE_BIT));
	else if (!stricmp(word,"TOPIC")) return (FunctionResult) ( result & (ENDSENTENCE_BIT|FAILSENTENCE_BIT|RETRYSENTENCE_BIT|ENDINPUT_BIT|RETRYINPUT_BIT));
	else if (!stricmp(word,"LOOP")) return (FunctionResult) ( result & (ENDTOPIC_BIT|FAILTOPIC_BIT|RETRYTOPIC_BIT| ENDSENTENCE_BIT|FAILSENTENCE_BIT|RETRYSENTENCE_BIT| ENDINPUT_BIT|RETRYINPUT_BIT));
	else if (!stricmp(word,"SENTENCE") || !stricmp(word,"INPUT")) return NOPROBLEM_BIT;
	return FAILRULE_BIT; // not a legal choice
}

static FunctionResult NotNullCode(char* buffer)
{
	FunctionResult result;
	Output(ARGUMENT(1),buffer,result);
	if (*buffer) *buffer = 0;
	else return FAILRULE_BIT;
	return NOPROBLEM_BIT;
}

static FunctionResult ResultCode(char* buffer)
{
	FunctionResult result;
	Output(ARGUMENT(1),buffer,result);
	*buffer = 0;
	strcpy(buffer,ResultCode(result));
	return NOPROBLEM_BIT;
}

static FunctionResult RetryCode(char* buffer)
{
	char* arg = ARGUMENT(1);
	if (!stricmp(arg,"TOPIC"))  return RETRYTOPIC_BIT;
	if (!stricmp(arg,"sentence"))  return RETRYSENTENCE_BIT;
	if (!stricmp(arg,"input"))  
		return RETRYINPUT_BIT;
	if (!stricmp(arg,"toprule"))  return RETRYTOPRULE_BIT;
	return RETRYRULE_BIT;
}

static WORDP memoryDict = 0;
static char* memoryText = 0;
static FACT* memoryFact = 0;

static WORDP memoryDictBase = 0;
static char* memoryTextBase = 0;
static FACT* memoryFactBase = 0;

FunctionResult MemoryMarkCode(char* buffer)
{
	memoryText = stringFree;
	memoryDict = dictionaryFree;
	memoryFact = factFree;
	return NOPROBLEM_BIT;
}

void SetBaseMemory()
{
	memoryTextBase = stringFree;
	memoryDictBase = dictionaryFree;
	memoryFactBase = factFree;
}

void ResetBaseMemory()
{
	ClearUserVariables(memoryTextBase); // reset any above and delete from list but leave alone ones below
	ResetFactSystem(memoryFactBase);// empties all fact sets and releases facts above marker
	ClearTemps();
	DictionaryRelease(memoryDictBase,memoryTextBase); // word & text
	ReportBug("Emergency Memory Reset\r\n");
	echo = true;
	Log(STDUSERLOG,"Emergency Memory Reset\r\n");
	echo = false;
}

FunctionResult MemoryFreeCode(char* buffer)
{
	if (!memoryText) return FAILRULE_BIT;
	ClearUserVariables(memoryText); // reset any above and delete from list but leave alone ones below
	ResetFactSystem(memoryFact);// empties all fact sets and releases facts above marker
	ClearTemps();
	DictionaryRelease(memoryDict,memoryText); // word & text
#ifndef DISCARDTESTING
	//bool oldecho = echo;
	//echo = true;
	//C_MemStats(buffer);
	//echo = oldecho;
#endif
	return NOPROBLEM_BIT;
}

FunctionResult AddContextCode(char* buffer)
{
	char* arg1 = ARGUMENT(1);
	unsigned int topic = (!strcmp(arg1,"~")) ? currentTopicID : FindTopicIDByName(arg1);
	if (!topic) return FAILRULE_BIT;
	AddContext(topic,ARGUMENT(2));
	return NOPROBLEM_BIT;
}

FunctionResult InContextCode(char* buffer)
{
	char* arg = ARGUMENT(1);
	char* dot = strchr(arg,'.');
	unsigned int topic = currentTopicID;
	if (dot) 
	{
		*dot = 0;
		topic = FindTopicIDByName(arg);
		arg = dot + 1;
	}
	unsigned int turn = InContext(topic,arg);
	if (turn == 0) return FAILRULE_BIT;
	sprintf(buffer,"%d",turn);
	return NOPROBLEM_BIT;
}

FunctionResult ArgumentCode(char* buffer)
{
	char* arg1 = ARGUMENT(1);
	char* arg2 = ARGUMENT(2);
	if (!IsDigit(*arg1) || !callIndex) return FAILRULE_BIT;	// must be number index within some call
	int d = callIndex - 1;// start of real
	while (*arg2 && d >=0)
	{
		if (!stricmp(callStack[d]->word,arg2)) break; // found named
		--d;
	}
	if (d < 0) return FAILRULE_BIT;	// could not find requested topic
	unsigned int arg = MACRO_ARGUMENT_COUNT(callStack[d]); // how many arguments can it handle
	unsigned int requestedArg = atoi(arg1);
	if (requestedArg == 0) return NOPROBLEM_BIT;  // just checking to see if caller exists
	if (requestedArg > arg) return FAILRULE_BIT;	// not a legal arg value, too high
	strcpy(buffer,callArgumentList[callArgumentBases[d]+requestedArg]);
	return NOPROBLEM_BIT;
}

//////////////////////////////////////////////////////////
/// DATABASE FUNCTIONS
//////////////////////////////////////////////////////////

#ifndef DISCARDDATABASE
#include "postgres/win32/libpq-fe.h"
static  PGconn     *usersconn; // shared db open stuff used instead of files for userwrites
static  PGconn     *conn; // shared db open stuff
static bool connDummy = false;

#ifdef WIN32
#pragma comment(lib, "../src/postgres/win32/libpq.lib")
#define MAKEWORDX(a, b)      ((unsigned short)(((BYTE)(((DWORD_PTR)(a)) & 0xff)) | ((unsigned short)((BYTE)(((DWORD_PTR)(b)) & 0xff))) << 8))
#endif

static FunctionResult DBCloseCode(char* buffer)
{
	if (!conn) 
	{
		if (connDummy)
		{
			connDummy = false;
			return NOPROBLEM_BIT;
		}
		char* msg = "db not open\r\n";
		SetUserVariable("$$db_error",msg);	// pass along the error
		Log(STDUSERLOG,msg);
		return FAILRULE_BIT;
	}

	PQfinish(conn);
	conn = NULL;
	return (buffer == NULL) ? FAILRULE_BIT : NOPROBLEM_BIT; // special call requesting error return (not done in script)
}

static FunctionResult PGUserFilesCloseCode(char* buffer)
{
	if (!usersconn) return FAILRULE_BIT;

	PGconn* hold = conn;
	conn = usersconn;
	FunctionResult result = DBCloseCode(buffer);
	if (result == NOPROBLEM_BIT) 
	{
		usersconn = NULL;
		memset((void*)&userFileSystem,0,sizeof(userFileSystem)); // drop user file system override
	}
	conn = hold;
	return result;
}

static FunctionResult DBInitCode(char* buffer)
{
	if (conn) 
	{
		char* msg = "DB already opened\r\n";
		SetUserVariable("$$db_error",msg);	// pass along the error
		if (trace & TRACE_SQL && CheckTopicTrace()) Log(STDUSERLOG,msg);
 		return FAILRULE_BIT;
	}
	char* ptr = ARGUMENT(1);
	char query[MAX_WORD_SIZE * 2];
	FunctionResult result;
	*query = 0;
	FreshOutput(ptr,query,result,0);
	if (result != NOPROBLEM_BIT) return result;
	if (!stricmp(query,"null"))
	{
		connDummy = true;
		return NOPROBLEM_BIT;
	}

#ifdef WIN32
	static bool first = true;
	if (first) // prevent DB close from closing WSAStartup to improve performance
	{
		first = false;
		WSADATA wsaData;
		unsigned short wVersionRequested = MAKEWORDX(2, 0);              //   Request WinSock v2.0
		if (WSAStartup(wVersionRequested, &wsaData) != 0) 
		{
			if (trace & TRACE_SQL && CheckTopicTrace()) Log(STDUSERLOG, "WSAStartup failed\r\n");
			return FAILRULE_BIT;
		}
	}
#endif
    /* Make a connection to the database */
    conn = PQconnectdb(query);

    /* Check to see that the backend connection was successfully made */
    if (PQstatus(conn) != CONNECTION_OK)
    {
		char msg[MAX_WORD_SIZE];
		sprintf(msg,"%s - %s\r\n",query,PQerrorMessage(conn));
		SetUserVariable("$$db_error",msg);	// pass along the error
        if (trace & TRACE_SQL && CheckTopicTrace()) Log(STDUSERLOG, "Connection failed: %s",  msg);
		return DBCloseCode(NULL);
    }

	return NOPROBLEM_BIT;
}

FILE* pguserCreate(const char* name){return NULL;}
FILE* pguserOpen(const char* name){return NULL;}
int pguserClose(FILE*){return 0;}
size_t pguserRead(void* buffer,size_t size, size_t count, FILE* file){return 0;}
size_t pguserWrite(const void* buffer,size_t size, size_t count, FILE* file){return 0;}
size_t pguserSize(FILE* file){return 0;}

static FunctionResult PGUserFilesCode(char* buffer)
{
	FunctionResult result = DBInitCode(buffer);
	if (result == NOPROBLEM_BIT)
	{
		static USERFILESYSTEM pgfiles = { pguserCreate, pguserOpen, pguserClose, pguserRead, pguserWrite, pguserSize};
		usersconn = conn;
		conn = NULL;
#ifdef INFORMATION
Normally user topic files are saved on the local filesystem using fopen, fclose, fread, fwrite, fseek, ftell calls.
If you want to store them elsewhere, like in a database, you can pass into InitSystem a nonnull USERFILESYSTEM block.
The pattern of calls is that the system will do a create or open call. A nonzero value will be passed around, but it doesnt really matter
because you can assume only one "FILE" is in use at a time so you can manage that with globals outside of CS. 
For writing, the system will  create the file (it should be "binary utf8"), perform a single write,  and then close it.
For reading, the system will first open it, ask for the size of its contents, then read once and close it.
	typedef FILE* (*UserFileCreate)(const char* name);
	typedef FILE* (*UserFileOpen)(const char* name);
	typedef int (*UserFileClose)(FILE*);
	typedef size_t (*UserFileRead)(void* buffer,size_t size, size_t count, FILE* file);
	typedef size_t (*UserFileWrite)(const void* buffer,size_t size, size_t count, FILE* file);
	typedef size_t (*UserFileSize)(FILE* file);
	memcpy((void*)&userFileSystem,pgfiles,sizeof(userFileSystem));

#endif



	}
	return result;
}
static FunctionResult DBExecuteCode(char* buffer)
{
	if (!conn) 
	{
		if (connDummy) return NOPROBLEM_BIT;

		char* msg = "DB not opened\r\n";
		SetUserVariable("$$db_error",msg);	// pass along the error
		if (trace & TRACE_SQL && CheckTopicTrace()) Log(STDUSERLOG,msg);
		return FAILRULE_BIT;
	}

	char* arg1 = ARGUMENT(1);
	PGresult   *res;
	FunctionResult result = NOPROBLEM_BIT;

	char query[MAX_WORD_SIZE * 2];
	char fn[MAX_WORD_SIZE];
	char* ptr = ReadCommandArg(arg1,query,result,OUTPUT_NOQUOTES|OUTPUT_EVALCODE|OUTPUT_NOTREALBUFFER); 
	if (result != NOPROBLEM_BIT) return result;
	ReadCommandArg(ptr,fn,result,OUTPUT_NOQUOTES|OUTPUT_EVALCODE|OUTPUT_NOTREALBUFFER); 
	if (result != NOPROBLEM_BIT) return result;

	// convert \" to " within params
	char* fix;
	while ((fix = strchr(query,'\\'))) memmove(fix,fix+1,strlen(fix)); // remove protective backslash

	// fix ' to '' inside a param
	fix = query;
	while ((fix = strchr(fix,'\''))) 
	{
		char* end = fix + 1;
		while ((end = strchr(end,'\''))) // finding end
		{
			if (end[1] == ' ' || end[1] == ';' || end[1] == '\t' || end[1] == '\n' || end[1]  == '\r' || end[1]  == ')'|| end[1]  == '('|| end[1]  == ',') // real end of token
			{
				fix = end;
				break;
			}
			else // internal ' needs converting
			{
				memmove(end+1,end,strlen(end)+1); 
				end[1] = '\'';
				end = end + 2;  // continue with real find
				fix = end - 1; // should we find no real end, this will move us past
			}
		}
		++fix; // always make progress
	}

	// adjust function reference name
	char* function = fn;
	if (*function == '\'') ++function; // skip over the ' 

	unsigned int argflags = 0;
	WORDP FN = (*function) ? FindWord(function) : NULL;
	if (FN) argflags = FN->x.macroFlags;

	if (trace & TRACE_SQL && CheckTopicTrace()) Log(STDUSERLOG, "DBExecute command %s\r\n", query);
    res = PQexec(conn, query);
	int status = (int) PQresultStatus(res);
    if (status == PGRES_BAD_RESPONSE ||  status == PGRES_FATAL_ERROR || status == PGRES_NONFATAL_ERROR)
    {
		char* msg = PQerrorMessage(conn);
		SetUserVariable("$$db_error",msg);	// pass along the error
        if (trace & TRACE_SQL && CheckTopicTrace()) Log(STDUSERLOG, "DBExecute command failed: %s %s status:%d\r\n", arg1,msg,status);
        PQclear(res);
		return FAILRULE_BIT;
     }
	if (*function && status == PGRES_TUPLES_OK) // do something with the answers
	{
		char psBuffer[MAX_WORD_SIZE * 4];
		psBuffer[0] = '(';
		psBuffer[1] = ' ';
	
		// process answers
		unsigned int limit = (unsigned int) PQntuples(res);
		unsigned int fields = (unsigned int) PQnfields(res);

		for (unsigned int i = 0; i < limit; i++) // for each row
		{
			char* at = psBuffer+2;
			for (unsigned int j = 0; j < fields; j++) 
			{
				// char *PQfname(const PGresult *res,int column_number); // get colum name
				// int PQfnumber(const PGresult *res, const char *column_name);
				Oid type = PQftype(res, j);
				bool keepQuotes = (argflags & ( 1 << j)) ? 1 : 0; // want to use quotes 

				*at = 0;
				char* val = PQgetvalue(res, i, j);
				if (keepQuotes)
				{
					*at++ = '"';
					strcpy(at,val);
					char* x = at;
					while ((x = strchr(x,'"'))) // protect internal quotes
					{
						memmove(x+1,x,strlen(x)+1);
						*x = '\\';
						x += 2;
					}
					at += strlen(at);
					*at++ = '"';
				}
				else // normal procesing
				{
					sprintf(at,"%s",val);
					at += strlen(at);
				}
				*at++ = ' ';

				if ((at - psBuffer) > ((MAX_WORD_SIZE * 4)-100)) 
				{
					ReportBug("postgres answer overflow %s -> %s\r\n",query,psBuffer);
					break;
				}
			}
			*at = 0;
			strcpy(at,")"); //  ending paren
			if (trace & TRACE_SQL && CheckTopicTrace()) Log(STDUSERLOG, "DBExecute results %s\r\n", psBuffer);
	
 			if (stricmp(function,"null")) DoFunction(function,psBuffer,buffer,result); 
			buffer += strlen(buffer);
			if (result != 0) 
			{
				if (result == UNDEFINED_FUNCTION) result = FAILRULE_BIT;
				char msg[MAX_WORD_SIZE];
				sprintf(msg,"Failed %s%s\r\n",function,psBuffer);
				SetUserVariable("$$db_error",msg);	// pass along the error
 				if (trace & TRACE_SQL && CheckTopicTrace()) Log(STDUSERLOG,msg);
				break; // failed somehow
			}
		}
	}

	PQclear(res);
	return result;
} 

#endif
	
//////////////////////////////////////////////////////////
/// WORD MANIPULATION
//////////////////////////////////////////////////////////

static FunctionResult BurstCode(char* buffer) //   take value and break into facts of burst-items as subjects
{//   ^burst(^cause : )   1: data source 2: burst character  optional 0th argument is WORDCOUNT

	//   prepare spot to store pieces
	MEANING verb;
	MEANING object;
	if (impliedWild != ALREADY_HANDLED)  SetWildCardIndexStart(impliedWild); //   start of wildcards to spawn
	object = verb = Mburst;
	*buffer = 0;
	bool count = false;
	char* ptr = ARGUMENT(1); //   what to burst
	if (!*ptr) return NOPROBLEM_BIT;
	if (*ptr == '"' ) // if a quoted string, remove the quotes
	{
		++ptr;
		size_t len = strlen(ptr);
		if (ptr[len-1] == '"') ptr[len-1] = 0;
	}
	bool once = false;

	if (!stricmp(ptr,"wordcount")) 
	{
		count = true;
		strcpy(ARGUMENT(1),ARGUMENT(2));
		ptr = ARGUMENT(1);
		strcpy(ARGUMENT(2),ARGUMENT(3));
		strcpy(ARGUMENT(3),ARGUMENT(4));
	}
	else if (!stricmp(ptr,"once")) 
	{
		once = true;
		strcpy(ARGUMENT(1),ARGUMENT(2));
		ptr = ARGUMENT(1);
		strcpy(ARGUMENT(2),ARGUMENT(3));
		strcpy(ARGUMENT(3),ARGUMENT(4));
	}

	unsigned int counter = 1;

	//   get string to search for. If quoted, remove the quotes
	char* scan = ARGUMENT(2);	//   how to burst
	char* scan1 = NULL;

	if (!*scan) 
	{
		scan = " "; // default is space AND OR _
		scan1 = "_";
	}
	else // clear any special characters
	{
		char* find;
		while ((find = strstr(scan,"\\r"))) // convert cr
		{
			*find = '\r';
			memmove(find+1,find+2,strlen(find)+1);
		}
		while ((find = strstr(scan,"\\n"))) // convert cr
		{
			*find = '\n';
			memmove(find+1,find+2,strlen(find)+1);
		}
		while ((find = strstr(scan,"\\t"))) // convert cr
		{
			*find = '\t';
			memmove(find+1,find+2,strlen(find)+1);
		}
	}
	if (*scan == '"' ) // if a quoted string as burst char, remove the quotes
	{
		++scan;
		size_t len = strlen(scan);
		if (scan[len-1] == '"') scan[len-1] = 0;
	}
	if (*ptr == '"' ) // if a quoted string, remove the quotes
	{
		++ptr;
		size_t len = strlen(ptr);
		if (ptr[len-1] == '"') ptr[len-1] = 0;
	}

	//   loop that splits into pieces and stores them

	char* hold = strstr(ptr,scan);
	char* hold1 = (scan1) ? strstr(ptr,scan1) : NULL;
	if (!hold) hold = hold1; // only has second
	if (hold1 && hold1 < hold) hold = hold1; // sooner
	size_t scanlen = strlen(scan);
	if (impliedSet != ALREADY_HANDLED) SET_FACTSET_COUNT(impliedSet,0);
	while (hold)
	{
		*hold = 0;	//   terminate first piece
		if (*ptr == 0) {;} // null piece - breaking here makes no sense at start
		else if (count) ++counter;
		if (trace) Log(STDUSERLOG,"burst: %s ",ptr);
		//   store piece before scan marker
		if (impliedWild != ALREADY_HANDLED)  SetWildCard(ptr,ptr,0,0);
		else if (impliedSet != ALREADY_HANDLED)
		{
			if (*ptr)
			{
				MEANING T = MakeMeaning(StoreWord(ptr));
				FACT* F = CreateFact(T, verb,object,FACTTRANSIENT|FACTDUPLICATE);
				AddFact(impliedSet,F);
			}
		}
		else //   dump straight to output buffer, first piece only
		{
			strcpy(buffer,ptr);
			break;
		}

		ptr = hold + scanlen; //   ptr after scan marker
		hold = strstr(ptr,scan);
		hold1 = (scan1) ? strstr(ptr,scan1) : NULL;
		if (!hold) hold = hold1; // only has second
		if (hold1 && hold1 < hold) hold = hold1; // sooner
		if (once) break;
	}

	//   assign the last piece
	char result[MAX_WORD_SIZE];
	if (count) // just doing count
	{
		sprintf(result,"%d",counter);
		ptr = result;
	}
	if (trace) Log(STDUSERLOG,"burst: %s ",ptr);
	if (impliedWild != ALREADY_HANDLED)  
	{
		SetWildCard(ptr,ptr,0,0);
		SetWildCard("","",0,0); // clear next one
	}
	else if (impliedSet != ALREADY_HANDLED)
	{
		if (*ptr) AddFact(impliedSet,CreateFact(MakeMeaning(StoreWord(ptr)), verb,object,FACTTRANSIENT|FACTDUPLICATE));
	}
	else if (!*buffer) strcpy(buffer,ptr);
	impliedSet = impliedWild = ALREADY_HANDLED;	//   we did the assignment
	return NOPROBLEM_BIT;
}

static FunctionResult ExplodeCode(char* buffer) //   take value and break into facts of burst-items as subjects
{
	//   prepare spot to store pieces
	MEANING verb;
	MEANING object;
	if (impliedWild != ALREADY_HANDLED)  SetWildCardIndexStart(impliedWild); //   start of wildcards to spawn
	object = verb = Mburst;
	*buffer = 0;

	char* ptr = ARGUMENT(1) - 1; //   what to explode
	char word[MAX_WORD_SIZE];
	word[1] = 0;
	SET_FACTSET_COUNT(impliedSet,0);
	while (*++ptr)
	{
		*word = *ptr;
		//   store piece before scan marker
		if (impliedWild != ALREADY_HANDLED)  SetWildCard(word,word,0,0);
		else if (impliedSet != ALREADY_HANDLED)
		{
			MEANING T = MakeMeaning(StoreWord(word));
			FACT* F = CreateFact(T, verb,object,FACTTRANSIENT);
			AddFact(impliedSet,F);
		}
		else //   dump straight to output buffer, first piece only
		{
			strcpy(buffer,word);
			break;
		}
	}
	impliedSet = impliedWild = ALREADY_HANDLED;	
	return NOPROBLEM_BIT;
}

static FunctionResult FlagsCode(char* buffer)
{
	WORDP D = FindWord(ARGUMENT(1));
	if (!D) return FAILRULE_BIT;
#ifdef WIN32
	sprintf(buffer,"%I64d",D->systemFlags); 
#else
	sprintf(buffer,"%lld",D->systemFlags); 
#endif
	return NOPROBLEM_BIT;
}

static FunctionResult UppercaseCode(char* buffer)
{
	strcpy(buffer, (IsUpperCase(ARGUMENT(1)[0])) ? (char*) "1" : (char*) "0");
	return NOPROBLEM_BIT;
}

static FunctionResult PropertiesCode(char* buffer)
{
	char* arg1 = ARGUMENT(1);
	WORDP D = FindWord(arg1);
	if (!D) return FAILRULE_BIT;
#ifdef WIN32
	sprintf(buffer,"%I64d",D->properties); 
#else
	sprintf(buffer,"%lld",D->properties); 
#endif
	return NOPROBLEM_BIT;
}

static char* NextWord(char* ptr, WORDP& D,bool canon)
{
	char word[MAX_WORD_SIZE];
	ptr = ReadCompiledWord(ptr,word);
	MakeLowerCase(word);
	if (canon)
	{
		WORDP entry,canonical;
		uint64 sysflags = 0;
		uint64 cansysflags = 0;
		GetPosData(2,word,entry,canonical,sysflags,cansysflags); 
		if (canonical) strcpy(word,canonical->word);
		else if (entry) strcpy(word,entry->word);
	}
	MakeLowerCase(word);
	D = StoreWord(word);
	return ptr;
}

static FunctionResult IntersectWordsCode(char* buffer)
{
	unsigned int store = (impliedSet == ALREADY_HANDLED) ? 0 : impliedSet;
	SET_FACTSET_COUNT(store,0);
	WORDP words[2000];
	int index = 0;

	char* arg1 = ARGUMENT(1);
	if (*arg1 == '"')
	{
		size_t len = strlen(arg1);
		if (arg1[len-1] == '"')
		{
			arg1[len-1] = 0;
			++arg1;
		}
	}
	Convert2Blanks(arg1);
	char* at = arg1;
	while ((at = strchr(at,'~'))) *at = ' '; 

	char* arg2 = ARGUMENT(2); 
	if (*arg2 == '"')
	{
		size_t len = strlen(arg2);
		if (arg2[len-1] == '"')
		{
			arg2[len-1] = 0;
			++arg2;
		}
	}
	Convert2Blanks(arg2);
	at = arg2;
	while ((at = strchr(at,'~'))) *at = ' '; 

	bool canon = (!stricmp(ARGUMENT(3),"canonical"));
	WORDP D;
	while (*arg1)
	{
		arg1 = NextWord(arg1,D,canon);
		AddInternalFlag(D,INTERNAL_MARK);
		words[++index] = D;
	}

	unsigned int count = 0;
	if (index) 
	{
		while (*arg2) 
		{
			arg2 = NextWord(arg2,D,canon);
			if (D->internalBits & INTERNAL_MARK)
			{
				FACT* old = factFree;
				FACT* F = CreateFact(MakeMeaning(D),Mintersect,MakeMeaning(D),FACTTRANSIENT);
				if (old != factFree) 
				{
					AddFact(store,F);
					count = 1;
				}
			}
		}
	
		while (index) RemoveInternalFlag(words[index--],INTERNAL_MARK);
	}

	if (impliedSet == ALREADY_HANDLED && count == 0) return FAILRULE_BIT;
	return NOPROBLEM_BIT;
}

static FunctionResult JoinCode(char* buffer) 
{     
	char* original = buffer;
	char* ptr = ARGUMENT(1);
	bool autospace = false;
	if (!strnicmp(ptr,"AUTOSPACE",9))
	{
		autospace = true;
		ptr += 10;
	}
    while (ptr)
	{
		char word[MAX_WORD_SIZE];
		char* at = ReadCompiledWord(ptr,word); 
        if (*word == ')' || !*word) break; //   done
		size_t len = strlen(word);
		if (*word == '"' && word[1] == ' ' && word[2] == '"') // pure simple space
		{
			strcpy(buffer," ");
			ptr = at;
		}
		else if (*word == '"' && word[1] ==  FUNCTIONSTRING) // compiled code being joined
		{
			FunctionResult result = NOPROBLEM_BIT;
			ReformatString(word+2,buffer,result,0);
			if (result != NOPROBLEM_BIT) return result;
			ptr = at;
		}
		else if (*word == '"' && word[len-1] == '"')
		{
			word[len-1] = 0;
			strcpy(buffer,word+1);
			ptr = at;
		}
 		else 
		{
			FunctionResult result;
			ptr = ReadShortCommandArg(ptr,word,result);
			if (result & ENDCODES) return result;
			strcpy(buffer,word);
		}
		if (trace & TRACE_OUTPUT && CheckTopicTrace()) Log(STDUSERLOG,"%s ",buffer);
		bool did = *buffer != 0;
		buffer += strlen(buffer);
		if (autospace && did) *buffer++ = ' '; 
    }
	if (autospace && original != buffer) *--buffer = 0;
	if (trace & TRACE_OUTPUT && CheckTopicTrace()) Log(STDUSERLOG,") = %s ",original);
 	return NOPROBLEM_BIT;
}

static FunctionResult PhraseCode(char* buffer)
{
	char* arg = ARGUMENT(1);
	char posn[MAX_WORD_SIZE];
	char type[MAX_WORD_SIZE];
	bool canonical = false;
	unsigned int n;
	arg = ReadCompiledWord(arg,type);
	arg = ReadCompiledWord(arg,posn);
	if (!strnicmp(arg,"canonical",9)) canonical = true;
	if (*posn == '\'') memmove(posn,posn+1,strlen(posn));
	if (IsDigit(*posn))
	{
		unsigned int n = atoi(posn);
		if (n == 0 || n > wordCount) return FAILRULE_BIT;
	}
	else if (*posn == '_')  n = WildPosition(posn);
	else if (*posn == '^') 
	{
		char word[MAX_WORD_SIZE];
		ReadArgument(posn,word);
		n = atoi(word);
	}
	else if (*posn == '$') n = atoi(GetUserVariable(posn));
	else return FAILRULE_BIT;
	unsigned int i = n;
	if (!stricmp(type,"noun")) // noun phrase
	{
		if (roles[i] & (MAINOBJECT|MAINSUBJECT) && verbals[i]) // like "to play football"
		{
			unsigned int x = verbals[i];
			if (!x) return FAILRULE_BIT;
			while (i && verbals[--i] & x){;}
			while (verbals[++n] & x){;};
			--n;
		}
		else if (roles[i] & (MAINOBJECT|MAINSUBJECT) && clauses[i]) // "I like *whatever tastes good"
		{
			unsigned int x = clauses[i];
			if (!x) return FAILRULE_BIT;
			while (i && clauses[--i] & x){;}
			while (clauses[++n] & x){;};
			--n;
		}		
		else while (posValues[--i] & (ADJECTIVE_BITS|DETERMINER_BITS|POSSESSIVE|ADVERB)){;}
		// for now ignore , and conjunct coord grabbing like "my fat, luxurious file"
	}
	else if (!stricmp(type,"preposition")) // prep phrase
	{
		unsigned int x = phrases[n];
		if (!x) return FAILRULE_BIT;
		if (phrases[x] & phrases[startSentence])
		{
			strcat(buffer,wordStarts[startSentence]);
			strcat(buffer,"_");
			strcat(buffer,wordStarts[n]);
		}
		else while (i && phrases[--i] & x){;}
		while (phrases[n+1] == x) ++n;	// find actual end
	}
	else if (!stricmp(type,"verbal")) // verbal phrase
	{
		unsigned int x = verbals[n];
		if (!x) return FAILRULE_BIT;
		while (i && verbals[++i] & x){;}
		unsigned int tmp = i-1;
		i = n;
		n = tmp;
	}
	else if (!stricmp(type,"adjective")) // complement phrase
	{
		while (posValues[--i] & (ADJECTIVE_BITS|ADVERB)){;}
	}
	else return FAILRULE_BIT;
	if (n > wordCount) return FAILRULE_BIT;
	while (++i <= n)
	{
		if (canonical) strcat(buffer,wordCanonical[i]);
		else strcat(buffer,wordStarts[i]);
		if (i != n) strcat(buffer,"_");
	}
	return NOPROBLEM_BIT;
}

static FunctionResult English_POSCode(char* buffer)
{
	char* arg1 = ARGUMENT(1);
	char* arg2 = ARGUMENT(2);
	char* arg3 = ARGUMENT(3);
	if (!stricmp(arg1,"raw"))
	{
		int n = atoi(arg2);
		if (n < 1 || n > (int)wordCount) return FAILRULE_BIT;
		strcpy(buffer,wordStarts[n]);
		return NOPROBLEM_BIT;
	}
	if (!stricmp(arg1,"conjugate"))
	{
		int64 pos;
		ReadInt64(arg3,pos);
		if (pos & (VERB_PRESENT_PARTICIPLE | NOUN_GERUND))
		{
			strcpy(arg1,"verb");
			strcpy(arg3,"present_participle");
			English_POSCode(buffer);
		}
		else if (pos & VERB_PAST_PARTICIPLE) 
		{
			strcpy(arg1,"verb");
			strcpy(arg3,"past_participle");
			English_POSCode(buffer);
		}
		else if (pos & VERB_PAST) 
		{ 
			if (!stricmp(arg2,"be") && pos & SINGULAR_PERSON) strcpy(buffer,"was"); // for 1st and 3rd person singular,  default is were
			else
			{
				strcpy(arg1,"verb");
				strcpy(arg3,"past");
				English_POSCode(buffer);
			}
		}
		else if (pos & VERB_PRESENT) 
		{ 
			if (!stricmp(arg2,"be") && pos & SINGULAR_PERSON) strcpy(buffer,"am"); // default is is. good for are
			else
			{
				strcpy(arg1,"verb");
				strcpy(arg3,"present");
				English_POSCode(buffer);
			}
		}
		else if (pos & VERB_PRESENT_3PS) 
		{ 
			strcpy(arg1,"verb");
			strcpy(arg3,"present3ps");
			English_POSCode(buffer);
		}
		else if (pos & NOUN_PLURAL || pos & NOUN_PROPER_PLURAL)
		{
			strcpy(arg1,"noun");
			strcpy(arg3,"plural");
			English_POSCode(buffer);
		}
		else if (pos & PLACE_NUMBER)
		{
			size_t len = strlen(arg2);
			char c = arg2[len-1];
			if (c == '1') sprintf(buffer,"%sst",arg2);
			else if (c == '2') sprintf(buffer,"%snd",arg2); 
			else if (c == '3') sprintf(buffer,"%srd",arg2);
			else if (IsDigit(*arg2)) sprintf(buffer,"%sth",arg2);
			else strcpy(buffer,arg2); // first, second, third etc
		}
		else if (pos & MORE_FORM && pos & ADJECTIVE) 
		{ 
			strcpy(arg1,"adjective");
			strcpy(arg3,"more");
			English_POSCode(buffer);
		}
		else if (pos & MOST_FORM && pos & ADJECTIVE) 
		{ 
			strcpy(arg1,"adjective");
			strcpy(arg3,"most");
			English_POSCode(buffer);
		}
		else if (pos & MORE_FORM && pos & ADVERB) 
		{ 
			strcpy(arg1,"adverb");
			strcpy(arg3,"more");
			English_POSCode(buffer);
		}
		else if (pos & MOST_FORM && pos & ADVERB) 
		{ 
			strcpy(arg1,"adverb");
			strcpy(arg3,"most");
			English_POSCode(buffer);
		}
		else if (pos & PRONOUN_POSSESSIVE) 
		{ 
			if (!stricmp(arg2,"he")) strcpy(buffer,"his"); // currently we keep pronouns as is, but we might use canonical on them
			else if (!stricmp(arg2,"his")) strcpy(buffer,"his");
			else if (!stricmp(arg2,"she")) strcpy(buffer,"her");
			else if (!stricmp(arg2,"her")) strcpy(buffer,"her");
			else if (!stricmp(arg2,"it")) strcpy(buffer,"its");
			else if (!stricmp(arg2,"its")) strcpy(buffer,"its");
			else if (!stricmp(arg2,"they")) strcpy(buffer,"their");
			else if (!stricmp(arg2,"their")) strcpy(buffer,"their");
			else if (!stricmp(arg2,"you")) strcpy(buffer,"your");
			else if (!stricmp(arg2,"my")) strcpy(buffer,"my");
			else if (!stricmp(arg2,"I")) strcpy(buffer,"my");
		}
		else if (pos & PRONOUN_OBJECT) 
		{ 
			if (!stricmp(arg2,"he")) strcpy(buffer,"him");
			else if (!stricmp(arg2,"she")) strcpy(buffer,"her");
			else if (!stricmp(arg2,"I")) strcpy(buffer,"me");
			else if (!stricmp(arg2,"they")) strcpy(buffer,"them");
			else if (!stricmp(arg2,"him")) strcpy(buffer,"him");
			else if (!stricmp(arg2,"her")) strcpy(buffer,"her");
			else if (!stricmp(arg2,"me")) strcpy(buffer,"me");
			else if (!stricmp(arg2,"them")) strcpy(buffer,"them");
		else strcpy(buffer,arg2);
		}
		else strcpy(buffer,arg2);
		return NOPROBLEM_BIT;
	}
	if (!stricmp(arg1,"syllable"))
	{
		sprintf(buffer,"%d",ComputeSyllables(arg2));
		return NOPROBLEM_BIT;
	}
	if (!stricmp(arg1,"hex64"))
	{
		int64 num;
		ReadInt64(arg2,num);
#ifdef WIN32
		sprintf(buffer,"0x%016I64x",num);
#else
		sprintf(buffer,"0x%016llx",num); 
#endif
		return NOPROBLEM_BIT;
	}
	if (!stricmp(arg1,"hex32"))
	{
		unsigned int num;
		ReadInt(arg2,num);
		sprintf(buffer,"0x%08x",num);
		return NOPROBLEM_BIT;
	}
	if (!stricmp(arg1,"type"))
	{
		if (*arg2 == '~') strcpy(buffer,"concept");
		else if (IsDigit(*arg2)) strcpy(buffer,"number");
		else if (IsAlphaUTF8(*arg2)) strcpy(buffer,"word");
		else strcpy(buffer,"unknown");
		return NOPROBLEM_BIT;
	}
	if (!stricmp(arg1,"common"))
	{
		if (!arg2) return FAILRULE_BIT;
		WORDP D = FindWord(arg2,0,PRIMARY_CASE_ALLOWED);
		if (!D) return NOPROBLEM_BIT;
		uint64 level = (D->systemFlags & COMMON7);
		level >>= (64-14);
		sprintf(buffer,"%d",(int)level);
		return NOPROBLEM_BIT;
	}
	if (!stricmp(arg1,"verb"))
	{
		if (!arg2) return FAILRULE_BIT;
		char word[MAX_WORD_SIZE];
		MakeLowerCopy(word,arg2);
		char* infin = English_GetInfinitive(word,true); 
		if (!infin) infin = word;
		if (!stricmp(arg3,"present_participle")) 
		{
			char* use = English_GetPresentParticiple(word);
			if (!use) return FAILRULE_BIT;
			strcpy(buffer,use);
		}
		else if (!stricmp(arg3,"past_participle")) 
		{
			char* use = English_GetPastParticiple(word);
			if (!use) return FAILRULE_BIT;
			strcpy(buffer,use);
		}
		else if (!stricmp(arg3,"infinitive")) 
		{
			char* verb = English_GetInfinitive(word,true);
			strcpy(buffer,verb);
		}
		else if (!stricmp(arg3,"past")) 
		{
			char* past = English_GetPastTense(infin);
			if (!past) return FAILRULE_BIT;
			strcpy(buffer,past);
		}
		else if (!stricmp(arg3,"present3ps")) 
		{
			char* third = English_GetThirdPerson(infin);
			if (!third) return FAILRULE_BIT;
			strcpy(buffer,third);
		}
		else if (!stricmp(arg3,"present")) 
		{
			char* third = English_GetPresent(infin);
			if (!third) return FAILRULE_BIT;
			strcpy(buffer,third);
		}
		else if (!stricmp(arg3,"match"))
		{
			char* arg4 = ARGUMENT(4);
			WORDP D = FindWord(arg4);
			char* plural = English_GetPluralNoun(D);
			char* verb;
			if (!plural || stricmp(plural,arg4)) // singular noun
			{
				verb = English_GetThirdPerson(arg2);
				if (verb)  strcpy(buffer,verb);
			}
			else // plural noun
			{
				verb = English_GetInfinitive(arg2,false);
				if (verb) 
				{
					if (!stricmp(verb,"be")) strcpy(buffer,"are");
					else strcpy(buffer,verb);
				}
			}
			if (!*buffer) strcpy(buffer,arg2);
		}
		if (IsUpperCase(ARGUMENT(2)[0])) *buffer = GetUppercaseData(*buffer);
		return NOPROBLEM_BIT;
	}
	else if (!stricmp(arg1,"aux"))
	{
		if (!arg2) return FAILRULE_BIT;
		char word[MAX_WORD_SIZE];
		MakeLowerCopy(word,ARGUMENT(2));
		char* result = word;
   
		if (!strcmp(arg2,"do")) //   present tense
		{
			if (strcmp(arg3,"I") && strcmp(arg3,"you")) result = "does"; 
			else result = "do";
		}
		else if (!strcmp(arg2,"have")) 
		{
			if (strcmp(arg3,"I") && strcmp(arg3,"you")) result = "has"; 
			else result = "have";
		}
		else if (!strcmp(arg2,"be")) 
		{
			if (!strcmp(arg3,"I") ) result = "am";
			else if (!strcmp(arg3,"you")) result = "are"; 
			else result = "is";
		}
		else if (!strcmp(arg2,"was") || !strcmp(arg2,"were")) //   past tense
		{
			if (!strcmp(arg3,"I") ) result = "was";
			result = "were";
		}
		else result = arg2;
		strcpy(buffer,result);
		if (IsUpperCase(arg2[0])) *buffer = GetUppercaseData(*buffer);
		return NOPROBLEM_BIT;
	}
	else if (!stricmp(arg1,"pronoun"))
	{
		if (!stricmp(arg3,"flip"))
		{
			unsigned int n = BurstWord(arg2,0);
			for (unsigned int i = 0; i < n; ++i)
			{
				char* word = GetBurstWord(i);
				if (!stricmp(word,"my")) word = "your";
				else if (!stricmp(word,"your")) word = "my";
				else if (!stricmp(word,"I")) word = "you";
				else if (!stricmp(word,"you")) word = "I";
				strcpy(buffer,word);
				buffer += strlen(buffer);
				if (i != (n-1)) strcpy(buffer," ");
				buffer += strlen(buffer);
			}
			return NOPROBLEM_BIT;
		}
	}
	else if (!stricmp(arg1,"adjective"))
	{
		if (!arg2) return FAILRULE_BIT;
		char word[MAX_WORD_SIZE];
		MakeLowerCopy(word,ARGUMENT(2));
		char* adj = word; 
		if (!stricmp(arg3,"more"))
		{
			char* more = English_GetAdjectiveMore(adj);
			if (!more) sprintf(buffer,"more %s",adj);
			else strcpy(buffer,more);
		}
		else if (!stricmp(arg3,"most"))
		{
			char* most = English_GetAdjectiveMost(adj);
			if (!most) sprintf(buffer,"most %s",adj);
			else strcpy(buffer,most);
		}
		return NOPROBLEM_BIT;
	}
	else if (!stricmp(arg1,"adverb"))
	{
		if (!arg2) return FAILRULE_BIT;
		char word[MAX_WORD_SIZE];
		MakeLowerCopy(word,ARGUMENT(2));
		char* adv = word; 
		if (!stricmp(arg3,"more"))
		{
			char* more = English_GetAdverbMore(adv);
			if (!more) sprintf(buffer,"more %s",adv);
			else strcpy(buffer,more);
		}
		else if (!stricmp(arg3,"most"))
		{
			char* most = English_GetAdverbMost(adv);
			if (!most) sprintf(buffer,"most %s",adv);
			else strcpy(buffer,most);
		}
		return NOPROBLEM_BIT;
	}
	else if (!stricmp(arg1,"noun"))
	{
		if (!stricmp(arg3,"proper")) 
		{
			// we know the word, use its known casing for spelling
			WORDP D = FindWord(arg2,0,UPPERCASE_LOOKUP);
			if (D)
			{
				strcpy(buffer,D->word);
				return NOPROBLEM_BIT;
			}

			// synthesize appropriate casing
			unsigned int n = BurstWord(arg2);
			for (unsigned int i = 0; i < n; ++i)
			{
				char* word = GetBurstWord(i);
				WORDP D = FindWord(word,0,LOWERCASE_LOOKUP);
				if (D && D->properties & LOWERCASE_TITLE); //   allowable particles and connecting words that can be in lower case
				else *word = GetUppercaseData(*word);
				strcat(buffer,word);
				if (i != (n-1)) strcat(buffer," ");
			}
			return NOPROBLEM_BIT;
		}
		if (!stricmp(arg3,"lowercaseexist"))	// lower case legal?
		{
			WORDP D = FindWord(arg2,0,LOWERCASE_LOOKUP);
			return (D) ? NOPROBLEM_BIT : FAILRULE_BIT;
		}
		if (!stricmp(arg3,"uppercaseexist"))	// upper case legal?
		{
			WORDP D = FindWord(arg2,0,UPPERCASE_LOOKUP);
			return (D) ? NOPROBLEM_BIT : FAILRULE_BIT;
		}

		char* noun =  English_GetSingularNoun(arg2,true,false);
		if (!noun) return NOPROBLEM_BIT;
		if (!stricmp(arg3,"singular") || (atoi(arg3) == 1 && !strchr(arg3,'.')) || !stricmp(arg3,"-1") || !stricmp(arg3,"one")) // allow number 1 but not float
		{
			strcpy(buffer,noun);
			return NOPROBLEM_BIT;		
		}
		else if (!stricmp(arg3,"plural") || IsDigit(arg3[0]) || (*arg3 == '-' && IsDigit(arg3[1])) ) // allow number non-one and negative 1
		{
			//   swallow the args. for now we KNOW they are wildcard references
			char* plural = English_GetPluralNoun(StoreWord(noun));
			if (!plural) return NOPROBLEM_BIT;
			strcpy(buffer,plural);
			return NOPROBLEM_BIT;
		}
		else if (!stricmp(arg3,"irregular") ) // generate a response only if plural is irregular from base (given)
		{
			//   swallow the args. for now we KNOW they are wildcard references
			char* plural = English_GetPluralNoun(StoreWord(noun));
			if (!plural) return NOPROBLEM_BIT;
			size_t len = strlen(noun);
			if (strnicmp(plural,noun,len)) strcpy(buffer,plural); // show plural when base not in it
			return NOPROBLEM_BIT;
		}
	}
	else if (!stricmp(arg1,"determiner")) //   DETERMINER noun
	{
		size_t len = strlen(arg2);
		if (arg2[len-1] == 'g' && English_GetInfinitive(arg2,false)) //   no determiner on gerund
		{
			strcpy(buffer,arg2);
			return NOPROBLEM_BIT;
		}
		//   already has one builtinto the word or phrase
		if (!strnicmp(arg2,"a_",2) || !strnicmp(arg2,"an_",3) || !strnicmp(arg2,"the_",4)) 
		{
			strcpy(buffer,arg2);
			return NOPROBLEM_BIT;
		}

		WORDP D = FindWord(arg2);
		if (D && D->properties & (NOUN_PROPER_SINGULAR|NOUN_PROPER_PLURAL))  //no determiner, is mass or proper name
		{
			strcpy(buffer,arg2);
			return NOPROBLEM_BIT;
		}

		//   if a plural word, use no determiner
		char* s = English_GetSingularNoun(arg2,true,false);
		if (!s || stricmp(arg2,s)) //   if has no singular or isnt same, assume we are plural and add the
		{
			sprintf(buffer,"the %s",arg2);
			return NOPROBLEM_BIT;
		}

		//   provide the determiner now
		*buffer++ = 'a';
		*buffer = 0;
		if (IsVowel(*arg2)) *buffer++ = 'n'; //   make it "an"
		*buffer++ = ' ';	//   space before the word
		strcpy(buffer,arg2);
		return NOPROBLEM_BIT;
	}
	else if (!stricmp(arg1,"place"))
	{
		int value = (int)Convert2Integer(arg2);
		if ((value%10) == 1) sprintf(buffer,"%dst",value); 
		if ((value%10) == 2) sprintf(buffer,"%dnd",value);
		if ((value%10) == 3) sprintf(buffer,"%drd",value);
		else sprintf(buffer,"%dth",value);
		return NOPROBLEM_BIT;
	}
	else if (!stricmp(arg1,"capitalize") || !stricmp(arg1,"uppercase"))
	{
		strcpy(buffer,arg2);
		*buffer = GetUppercaseData(*buffer);
		return NOPROBLEM_BIT;
	}
	else if (!stricmp(arg1,"allupper"))
	{
		strcpy(buffer,arg2);
		MakeUpperCase(buffer);
		return NOPROBLEM_BIT;
	}
	else if (!stricmp(arg1,"lowercase"))
	{
		MakeLowerCopy(buffer,arg2);
		return NOPROBLEM_BIT;
	}
	else if (!stricmp(arg1,"canonical"))
	{
		WORDP entry,canonical;
		uint64 sysflags = 0;
		uint64 cansysflags = 0;
		GetPosData(2,arg2,entry,canonical,sysflags,cansysflags);
		if (canonical) strcpy(buffer,canonical->word);
		else if (entry) strcpy(buffer,entry->word);
		else strcpy(buffer,arg2);
		return NOPROBLEM_BIT;
	}

	else if (!stricmp(arg1,"integer"))
	{
		strcpy(buffer,arg2);
		char* period = strchr(arg2,'.');
		if (period)
		{
			float val = (float) atof(arg2);
			*period = 0;
			int vali = atoi(arg2);
			if ((float) vali == val) strcpy(buffer,arg2);
		}
		return NOPROBLEM_BIT;
	}
	return FAILRULE_BIT;
}

static void RhymeWord(WORDP D, uint64 flag)
{
	if (!(D->properties & (NOUN | VERB | ADJECTIVE | ADVERB | DETERMINER_BITS | PRONOUN_BITS | CONJUNCTION | PREPOSITION | AUX_VERB ))) return;
	if (D->word && !IsAlphaUTF8(*D->word)) return;
	if (D->properties & (NOUN_PROPER_SINGULAR | NOUN_PROPER_PLURAL | NOUN_TITLE_OF_ADDRESS)) return;	// want ordinary words
	if (strchr(D->word,'_') || strchr(D->word,'-') ) return; // only normal words and not multi words either

	char* tail = (char*) flag;
	size_t n = strlen(tail);
	size_t len = strlen(D->word);
	if (len <= n) return;  // too short to rhyme
	if (D->word[len-1] != tail[n-1] || D->word[len-2] != tail[n-2]) return;	// must end the same way for last 2 letters
	if (!stricmp(D->word,tail)) return; // cannot have whole match
	if (!IsVowel(tail[n-1]) && !IsVowel(tail[n-2]) && D->word[len-3] != tail[n-3]) return;	// if 2 consonant ending, vowel before must match also
	if ((len - n) > 3) return; // should be similar in size

	if (!IsVowel(tail[n-1]) && IsVowel(tail[n-2]) )// if vowel-consonant ending, then before must match type also
	{
		if (IsVowel(tail[n-3]) && IsVowel(D->word[len-3])){;}
		else if (!IsVowel(tail[n-3]) && !IsVowel(D->word[len-3])){;}
		else return;	// if 2 consonant ending, vowel before must match also
	}
	if (!IsVowel(tail[n-2]) && IsVowel(tail[n-1]) ) //if consonant vowel ending, then before must match character before also
	{
		if (tail[n-3] != D->word[len-3]) return;
	}

	if (FACTSET_COUNT(rhymeSet) >= 500) return; //   limit
	WORDP E = StoreWord("1");
	AddFact(spellSet,CreateFact(MakeMeaning(E,0),MakeMeaning(FindWord("word")),MakeMeaning(D,0),FACTTRANSIENT));
}

static FunctionResult RhymeCode(char* buffer) 
{   
	int set = (impliedSet == ALREADY_HANDLED) ? 0 : impliedSet;
	SET_FACTSET_COUNT(set,0);
	rhymeSet = set;
	WalkDictionary(RhymeWord,(uint64)ARGUMENT(1));
	if (FACTSET_COUNT(set))
	{
		impliedSet = ALREADY_HANDLED;
		return NOPROBLEM_BIT;
	}

	return FAILRULE_BIT;
}

static FunctionResult FindTextCode(char* buffer) 
{ 
	// what to search in
	char* target = ARGUMENT(1);
	if (!*target) return FAILRULE_BIT; 

	// find value
	char* find = ARGUMENT(2);
  	if (!*find) return FAILRULE_BIT;

	unsigned int start = atoi(ARGUMENT(3));
	if (start >= strlen(target)) return FAILRULE_BIT;

	if (!stricmp(ARGUMENT(4),"insensitive"))
	{
		MakeLowerCase(find);
		MakeLowerCase(target);
	}

    char* found;
	size_t len = strlen(find);
	while ((found = strstr(target+start,find))) // case sensitive
    {
		unsigned int offset = found - target;
		char word[MAX_WORD_SIZE];
		sprintf(buffer,"%d",(int)(offset + len)); // where it ended (not part of it)
		sprintf(word,"%d",(int)offset);
		SetUserVariable("$$findtext_start",word); // where it started
		break;
	}
	if (!found) 
		return FAILRULE_BIT;
	return NOPROBLEM_BIT;
}

static FunctionResult ExtractCode(char* buffer) 
{ 
	// what to search in
	char* target = ARGUMENT(1);
	if (!*target) return FAILRULE_BIT;
	size_t len = strlen(target);
	unsigned int start = atoi(ARGUMENT(2));
	unsigned int end = atoi(ARGUMENT(3));
	if (start >= len) return FAILRULE_BIT;
	if (end >= len) end = len;
	if (end < start) return FAILRULE_BIT; 
	strncpy(buffer,target+start,(end-start));
	buffer[(end-start)] = 0;
	return NOPROBLEM_BIT;
}

static FunctionResult SubstituteCode(char* buffer) 
{ 
	bool wordMode = GetLowercaseData(*ARGUMENT(1)) != 'c'; // is word or character
	char* original = buffer;	// for debug
	// adjust substitution value
	char* substituteValue = ARGUMENT(4);
	size_t substituteLen = strlen(substituteValue);
	if (substituteLen > 1 && *substituteValue == '"' && substituteValue[substituteLen-1] == '"') // quoted expression means use the interior of it
	{
		substituteValue[substituteLen-1] = 0; 
		++substituteValue;
		substituteLen -= 2; 
	}
	if (*substituteValue != '_') Convert2Blanks(substituteValue); // if we explicitly request _, use it

	// what to search in
	char copy[MAX_WORD_SIZE * 4];
	*copy = ' '; // protective leading blank for -1 test
	char* arg2 = ARGUMENT(2);
	strcpy(copy+1,arg2);
	char* target = copy+1;
	if (!*target) return FAILRULE_BIT; 

	// find value
	char* find = ARGUMENT(3);
  	if (!*find) return FAILRULE_BIT;
	size_t findLen = strlen(find);
	if (findLen > 1 && *find == '"' && find[findLen-1] == '"') // find of a quoted thing means use interior
	{
		find[findLen-1] = 0; 
		++find;
		findLen -= 2; 
	}

    char* found;
	bool changed = false;
	while ((found = strstr(target,find))) // case sensitive
    {
		// no partial matches
		if (wordMode)
		{
			char c = found[findLen];	
			if (IsAlphaUTF8OrDigit(c) || IsAlphaUTF8OrDigit(*(found-1))) // skip nonword match
			{
				target = found + findLen;
				continue;
			}
		}
		changed = true;

		// move the before
		size_t offset = found-target;
		strncpy(buffer,target,offset);   //   copy up to but not including pattern.
        buffer += offset;
        target += offset + findLen;

		// copy the replacement
		strcpy(buffer,substituteValue);
		buffer += substituteLen;
		*buffer = 0;
	}
	strcpy(buffer,target); // append the rest

	// check for FAIL request
	char* notify = ARGUMENT(5);
	if (*notify || impliedIf != ALREADY_HANDLED) return (changed) ? NOPROBLEM_BIT : FAILRULE_BIT; // if user wants possible failure result
	return NOPROBLEM_BIT;
}

static void SpellOne(WORDP D, uint64 data)
{
	char* match = (char*) data;
	if (FACTSET_COUNT(spellSet) >= 500) return; //   limit

	if (!(D->properties & (NOUN | VERB | ADJECTIVE | ADVERB | DETERMINER_BITS | PRONOUN_BITS | CONJUNCTION | PREPOSITION | AUX_VERB ))) return;
	if (D->word && !IsAlphaUTF8(*D->word)) return;
	if (D->properties & (NOUN_PROPER_SINGULAR | NOUN_PROPER_PLURAL | NOUN_TITLE_OF_ADDRESS)) return;	// want ordinary words
	if (strchr(D->word,'_') ) return; // only normal words and not multi words either
	if (MatchesPattern(D->word,match))
	{
		WORDP E = StoreWord("1");
		AddFact(spellSet,CreateFact(MakeMeaning(E,0),MakeMeaning(FindWord("word")),MakeMeaning(D,0),FACTTRANSIENT));
	}
}

static unsigned int  Spell(char* match, unsigned int set)
{
	char pattern[MAX_WORD_SIZE];
	SET_FACTSET_COUNT(set,0);
	if (match[1] == '-') match[1] = 0;	// change 4-letter to 4
	MakeLowerCopy(pattern,match);
	spellSet = set;
	WalkDictionary(SpellOne,(uint64)pattern);
    return FACTSET_COUNT(set);
}

static FunctionResult SpellCode(char* buffer) //- locates up to 100 words in dictionary matching pattern and stores them as facts in @0
{
#ifdef INFORMATION
Fails if no words are found. Words must begin with a letter and be marked as a part of speech
(noun,verb,adjective,adverb,determiner,pronoun,conjunction,prepostion).

Not all words are found in the dictionary. The system only stores singular nouns and base
forms of verbs, adverbs, and adjectives unless it is irregular.

Pattern is a sequence of characters, with * matching 0 or more characters and . matching
exactly one. Pattern must cover the entire string. Pattern may be prefixed with a number, which
indicates how long the word must be. E.g.

^spell("4*")	# retrieves 100 4-letter words
^spell("3a*")  # retrieves 3-letter words beginning with "a"
^spell("*ing") # retrieves words ending in "ing" 
#endif

	return (Spell(ARGUMENT(1),0)) ? NOPROBLEM_BIT : FAILRULE_BIT;
}

static FunctionResult SexedCode(char* buffer)
{
	WORDP D = FindWord(ARGUMENT(1));
	if (!D || !(D->properties & (NOUN_HE|NOUN_SHE))) strcpy(buffer,ARGUMENT(4)); //   it 
	else if (D->properties & NOUN_HE) strcpy(buffer,ARGUMENT(2)); //   he
	else strcpy(buffer,ARGUMENT(3)); //   she
	return NOPROBLEM_BIT;
}

static FunctionResult TallyCode(char* buffer)
{
	char* arg1 = ARGUMENT(1);
	if (!*arg1) return FAILRULE_BIT;
	WORDP D = StoreWord(arg1);
	char* arg2 = ARGUMENT(2);
	if (!*arg2 ) sprintf(buffer,"%d",GetWordValue(D));
	else SetWordValue(D,atoi(arg2));
	return NOPROBLEM_BIT;
}

#ifndef DISCARDCOUNTER
static FunctionResult WordCountCode(char* buffer)
{
	char* arg1 = ARGUMENT(1);
	if (!*arg1)	return FAILRULE_BIT;
	WORDP D = StoreWord(arg1);
	char* arg2 = ARGUMENT(2);
	if (!*arg2 ) sprintf(buffer,"%d",D->counter);
	else D->counter = atoi(arg2);
	return NOPROBLEM_BIT;
}
#endif

static char* xbuffer;

static void DWalker(WORDP D,uint64 fn)
{
	if (*D->word == '$' || *D->word == ':' || *D->word == '^' || *D->word == '~' || *D->word == '%' || *D->word == ENDUNIT || *D->word == '"') return; // not real stuff
	if (D->internalBits & HAS_SUBSTITUTE) return;
	if (D->properties & (PUNCTUATION |COMMA|PAREN|QUOTE )) return; // " will cause a crash
	if (strchr(D->word,' ')) return;
	FunctionResult result;
	char* function = (char*)fn;
	char word[MAX_WORD_SIZE];
	sprintf(word,"( %s )",D->word);
	DoFunction(function,word,xbuffer,result); 
	xbuffer += strlen(xbuffer);
}

static FunctionResult WalkDictionaryCode(char* buffer)
{
	FunctionResult result;
	xbuffer = buffer;
	char fn[MAX_WORD_SIZE];
	char* function = ReadCommandArg(ARGUMENT(1),fn,result,OUTPUT_NOQUOTES|OUTPUT_EVALCODE|OUTPUT_NOTREALBUFFER); 
	if (result != NOPROBLEM_BIT) return result;
	function = fn;
	if (*function == '\'') ++function; // skip over the ' 
	WalkDictionary(DWalker,(uint64)function);
	return NOPROBLEM_BIT;
}


//////////////////////////////////////////////////////////
/// DICTIONARY
//////////////////////////////////////////////////////////

static FunctionResult GetPropertyCodes(char* who,char* ptr, uint64 &val, uint64 &sysval,unsigned int &internalBits, unsigned int &parseBits)
{
	while (ptr && *ptr)
	{
		char arg[MAX_WORD_SIZE];
		ptr = ReadCompiledWord(ptr,arg);
		if (!*arg || *arg == ')') break;
		if (!stricmp(arg,"CONCEPT"))  
		{
			if (*who != '~') return FAILRULE_BIT; // must be a concept name
			internalBits = CONCEPT;
		}
	
		// fact marks
		else if (IsDigit(arg[0])) ReadInt64(arg,(int64&)sysval);
		else 
		{
			uint64 bits = FindValueByName(arg);
			if (bits) val |= bits;
			else {
				bits = FindSystemValueByName(arg);
				if (!bits) 
				{
					bits = FindParseValueByName(arg);
					if (!bits) Log(STDUSERLOG,"Unknown addproperty value %s\r\n",arg);
					else parseBits |= bits;
				}
				else sysval |= bits;
			}
		}
	}
	return (!sysval && !val) ? FAILRULE_BIT : NOPROBLEM_BIT;
}

static FunctionResult RemoveInternalFlagCode(char* buffer)
{
	char* ptr = ARGUMENT(1);
	char arg1[MAX_WORD_SIZE];
	FunctionResult result = NOPROBLEM_BIT;
	ptr = ReadCommandArg(ptr,arg1,result,OUTPUT_NOQUOTES|OUTPUT_EVALCODE|OUTPUT_NOTREALBUFFER);
	if (result != NOPROBLEM_BIT) return result;
	if (!*arg1) return FAILRULE_BIT;
	WORDP D = FindWord(arg1,0,PRIMARY_CASE_ALLOWED); // add property to dictionary word
	if (!D) return FAILRULE_BIT;
	char* arg2 = ARGUMENT(2);
	if (!stricmp(arg2,"HAS_SUBSTITUTE"))
	{
		D->internalBits &= -1 ^ HAS_SUBSTITUTE;
	}
	else return FAILRULE_BIT;
	return NOPROBLEM_BIT;
}

static FunctionResult AddPropertyCode(char* buffer)
{
	char* ptr = ARGUMENT(1);
	char arg1[MAX_WORD_SIZE];
	FunctionResult result = NOPROBLEM_BIT;
	if (*ptr == '@') ptr = ReadCompiledWord(ptr,arg1); // dont eval a set
	else ptr = ReadCommandArg(ptr,arg1,result,OUTPUT_NOQUOTES|OUTPUT_EVALCODE|OUTPUT_NOTREALBUFFER);
	if (result != NOPROBLEM_BIT) return result;
	if (!*arg1) return FAILRULE_BIT;
	WORDP D = NULL;
	unsigned int store = 0;
	unsigned int count = 0;
	if (*arg1 == '@') // add property to all facts in set either on a field or fact as a whole
	{
		store = GetSetID(arg1);
		if (store == ILLEGAL_FACTSET) return FAILRULE_BIT;
		count =  FACTSET_COUNT(store);
	}
	else  D = StoreWord(arg1,0); // add property to dictionary word
	char arg3 = *GetSetType(arg1);

	uint64 val = 0;
	uint64 sysval = 0;
	unsigned int internalBits = 0;
	unsigned int parseBits = 0;
	result = GetPropertyCodes(arg1,ptr,val,sysval,internalBits,parseBits);
	if (result != NOPROBLEM_BIT) return result;
	if (D) // add to dictionary entry
	{
		if (val & NOUN_SINGULAR && D->internalBits & UPPERCASE_HASH) //make it right
		{
			val ^= NOUN_SINGULAR;
			val |= NOUN_PROPER_SINGULAR;
		}
		AddProperty(D,val);
		AddSystemFlag(D,sysval);
		if (internalBits & CONCEPT) AddInternalFlag(D,(unsigned int)(CONCEPT|buildID)); 
	}
	else if (*arg1 == '@') // add to all properties of fact set
	{
		for (unsigned int i = 1; i <= count; ++i)
		{
			FACT* F = factSet[store][i];
			if (arg3 == 's') D = Meaning2Word(F->subject); 
			else if (arg3 == 'v') D = Meaning2Word(F->verb);
			else if (arg3 == 'o') D = Meaning2Word(F->object);
			else
			{
				F->flags |= val;
				if (trace & TRACE_INFER && CheckTopicTrace()) TraceFact(F);
			}
			if (D)
			{
				uint64 val1 = val;
				if (val1 & NOUN_SINGULAR && D->internalBits & UPPERCASE_HASH) //make it right
				{
					val1 ^= NOUN_SINGULAR;
					val1 |= NOUN_PROPER_SINGULAR;
				}
				AddProperty(D,val1);
				AddSystemFlag(D,sysval);
				if (trace & TRACE_INFER && CheckTopicTrace()) Log(STDUSERLOG," %s\n",D->word);
			}
		}
	}
	return NOPROBLEM_BIT;
}

static FunctionResult DefineCode(char* buffer)
{ 
	char* w = ARGUMENT(1);
	WORDP D = FindWord(w,0);
	if (!D) return NOPROBLEM_BIT;

	bool noun = false;
	bool verb = false;
	bool adjective = false;
	bool adverb = false;
	char* which = ARGUMENT(2);
	for (unsigned int i = 1; i <= GetMeaningCount(D); ++i)
	{
		MEANING T = GetMaster(GetMeaning(D,i)) | GETTYPERESTRICTION(GetMeaning(D,i));
		unsigned int index = Meaning2Index(T);
		WORDP E = Meaning2Word(T);
		char* gloss = GetGloss(E,index);
		unsigned int restrict = GETTYPERESTRICTION(T);
		if (gloss && restrict & NOUN && !noun && (!*which || !stricmp(which,"NOUN")))
		{
			if (verb) sprintf(buffer,"As a noun it means %s. ",gloss);
			else sprintf(buffer,"The noun %s means %s. ",ARGUMENT(1),gloss);
			buffer += strlen(buffer);
			noun = true;
        }
		else if (gloss && restrict & VERB && !verb && (!*which || !stricmp(which,"VERB")))
		{
			if (noun) sprintf(buffer,"As a verb it means %s. ",gloss);
			else sprintf(buffer,"The verb %s means %s. ",ARGUMENT(1),gloss);
			buffer += strlen(buffer);
			verb = true;
        }
		else if (gloss && restrict & ADJECTIVE && !noun && !verb && !adjective && (!*which  || !stricmp(which,"ADJECTIVE")))
		{
			sprintf(buffer,"The adjective %s means %s. ",ARGUMENT(1),gloss);
			buffer += strlen(buffer);
			adjective = true;
        }
 		else if (gloss && restrict & ADVERB && !adverb && !noun && !verb && !adjective && (!*which  || !stricmp(which,"ADVERB")))
		{
			sprintf(buffer,"The adverb %s means %s. ",ARGUMENT(1),gloss);
			buffer += strlen(buffer);
			adverb = true;
        }
	}
    return NOPROBLEM_BIT;
}

static void ArgFlags(uint64& properties, uint64& flags,unsigned int & internalbits)
{
	char* arg2 = ARGUMENT(2);
	char* arg3 = ARGUMENT(3);
	properties = FindValueByName(arg2);
	properties |= FindValueByName(arg3);
	properties |= FindValueByName(ARGUMENT(4));
	properties |= FindValueByName(ARGUMENT(5));
	properties |= FindValueByName(ARGUMENT(6));

	flags = FindSystemValueByName(arg2);
	flags |= FindSystemValueByName(arg3);
	flags |= FindSystemValueByName(ARGUMENT(4));
	flags |= FindSystemValueByName(ARGUMENT(5));
	flags |= FindSystemValueByName(ARGUMENT(6));

	internalbits = 0;
	if (!stricmp(arg2,"CONCEPT") || !stricmp(arg3,"CONCEPT") || !stricmp(ARGUMENT(4),"CONCEPT") || 
		!stricmp(ARGUMENT(5),"CONCEPT") || !stricmp(ARGUMENT(6),"CONCEPT"))
	{
		internalbits |= CONCEPT;
	}
	if (!stricmp(arg2,"TOPIC") || !stricmp(arg3,"TOPIC") || !stricmp(ARGUMENT(4),"TOPIC") || 
		!stricmp(ARGUMENT(5),"TOPIC") || !stricmp(ARGUMENT(6),"TOPIC"))
	{
		internalbits |= TOPIC;
	}
}

static FunctionResult HasAnyPropertyCode(char* buffer)
{
	WORDP canonical = NULL;
	uint64 dprop;
	uint64 dsys;
	char* arg = ARGUMENT(1);
	WORDP D = FindWord(arg,0,PRIMARY_CASE_ALLOWED);
	if (!D)  GetPosData(2,arg,D,canonical,dprop,dsys);  // WARNING- created dict entry if it doesnt exist yet
	else 
	{
		dsys = D->systemFlags;
		dprop = D->properties;
	}
	uint64 properties;
	uint64 flags;
	unsigned int internalbits;
	ArgFlags(properties,flags,internalbits);
	if ((internalbits & CONCEPT) && (D->internalBits & TOPIC))  internalbits ^= CONCEPT;
	return (dprop & properties || dsys & flags || D->internalBits & internalbits) ? NOPROBLEM_BIT : FAILRULE_BIT;
}

static FunctionResult HasAllPropertyCode(char* buffer)
{
	WORDP canonical = NULL;
	uint64 dprop = 0;
	uint64 dsys;
	char* arg = ARGUMENT(1);
	WORDP D = FindWord(arg,0,PRIMARY_CASE_ALLOWED);
		if (!D)  GetPosData(2,arg,D,canonical,dprop,dsys); 
	else 
	{
		dsys = D->systemFlags;
		dprop = D->properties;
	}
	uint64 properties;
	uint64 flags;
	unsigned int internalbits;
	ArgFlags(properties,flags,internalbits);
	if (!flags && !properties) return FAILRULE_BIT;
	if ((internalbits & CONCEPT) && (D->internalBits & TOPIC)) return FAILRULE_BIT;
	return ((dprop & properties) == properties && (dsys & flags) == flags && (D->internalBits & internalbits) == internalbits) ? NOPROBLEM_BIT : FAILRULE_BIT; // has all the bits given
}

static FunctionResult RemovePropertyCode(char* buffer)
{
	char* ptr = ARGUMENT(1);
	char arg1[MAX_WORD_SIZE];
	FunctionResult result = NOPROBLEM_BIT;
	if (*ptr == '@') ptr = ReadCompiledWord(ptr,arg1); // dont eval a set
	else ptr = ReadCommandArg(ptr,arg1,result,OUTPUT_NOQUOTES|OUTPUT_EVALCODE|OUTPUT_NOTREALBUFFER);
	if (result != NOPROBLEM_BIT) return result;
	char arg3 = *GetSetType(arg1);
	if (!*arg1) return FAILRULE_BIT;
	WORDP D = NULL;
	unsigned int store = 0;
	unsigned int count = 0;
	if (*arg1 == '@') 
	{
		store = GetSetID(arg1);
		if (store == ILLEGAL_FACTSET) return FAILRULE_BIT;
		count = FACTSET_COUNT(store);
	}
	else  D = StoreWord(arg1,0); 

	uint64 val = 0;
	uint64 sysval = 0;
	unsigned int internalBits = 0;
	unsigned int parseBits = 0;
	result = GetPropertyCodes(arg1,ptr,val,sysval,internalBits,parseBits);
	if (result != NOPROBLEM_BIT) return result;
	if (D) // remove to dictionary entry
	{
		RemoveProperty(D,val);
		RemoveSystemFlag(D,sysval);
	}
	else // remove to all properties of set
	{
		for (unsigned int i = 1; i <= count; ++i)
		{
			FACT* F = factSet[store][i];
			if (arg3 == 's') D = Meaning2Word(F->subject);
			else if (arg3 == 'v') D = Meaning2Word(F->verb);
			else if (arg3 == 'o') D = Meaning2Word(F->object); 
			else  
			{
				F->flags &= -1 ^ val;
				if (trace & TRACE_INFER && CheckTopicTrace()) TraceFact(F);
			}
			if (D)
			{
				RemoveProperty(D,val);
				RemoveSystemFlag(D,sysval);
				if (trace & TRACE_INFER && CheckTopicTrace()) Log(STDUSERLOG," %s\n",D->word);
			}
		}
	}
	return NOPROBLEM_BIT;
}


//////////////////////////////////////////////////////////
/// MULTIPURPOSE
//////////////////////////////////////////////////////////

static FunctionResult DisableCode(char* buffer) 
{
	char* arg1 = ARGUMENT(1);
	char* arg2 = ARGUMENT(2);
	if (!stricmp(arg1,"topic"))
	{
		if (!*arg2) return FAILRULE_BIT;
		int id = FindTopicIDByName(ARGUMENT(2));
		if (id) 
		{
			if (GetTopicFlags(id) & TOPIC_SYSTEM) return FAILRULE_BIT;
			if (!(GetTopicFlags(id) & TOPIC_BLOCKED)) AddTopicFlag(id,TOPIC_BLOCKED|TOPIC_USED);
			return NOPROBLEM_BIT;       
		}
	}
	else if (!stricmp(arg1,"rule")) // 1st one found
	{
		if (planning) return FAILRULE_BIT;
		int id = 0;
		unsigned int topic = currentTopicID;
		bool fulllabel;
		bool crosstopic;
		char* rule;
		char* dot = strchr(arg2,'.');
		if (*arg2 == '~') 
		{
			rule = currentRule;
			id = currentRuleID;
		}
		else if (dot && IsDigit(dot[1])) rule = GetRuleTag(topic,id,arg2);
		else rule = GetLabelledRule(topic,arg2,"",fulllabel,crosstopic,id,currentTopicID);
		if (!rule) return FAILRULE_BIT;
		SetRuleDisableMark(topic,id);
		return NOPROBLEM_BIT;
	}
	else if (!stricmp(arg1,"rejoinder"))
	{
		outputRejoinderRuleID = NO_REJOINDER;
		return NOPROBLEM_BIT;
	}
	else if (!stricmp(arg1,"outputrejoinder"))
	{
		outputRejoinderRuleID = NO_REJOINDER;
		return NOPROBLEM_BIT;
	}
	else if (!stricmp(arg1,"inputrejoinder"))
	{
		inputRejoinderRuleID = NO_REJOINDER;
		return NOPROBLEM_BIT;
	}
	else if (!stricmp(arg1,"save")) 
	{
		stopUserWrite = true;
		return NOPROBLEM_BIT;
	}
	else if (!stricmp(arg1,"write")) 
	{
		uint64 set = GetSetID(ARGUMENT(1));
		if (set == ILLEGAL_FACTSET) return FAILRULE_BIT;
		setControl &= -1 ^ (1 << set);
		return NOPROBLEM_BIT;
	}

	return FAILRULE_BIT;
}

static FunctionResult EnableCode(char* buffer)
{
	char* arg2 = ARGUMENT(2);
	if (!stricmp(ARGUMENT(1),"topic"))
	{
		 //   topic name to enable
		if (!*arg2) return FAILRULE_BIT;
		if (!stricmp(arg2,"all"))
		{
			for (unsigned int start = 1; start <= numberOfTopics; ++start) 
			{

				if (GetTopicFlags(start) & TOPIC_SYSTEM) continue;
				RemoveTopicFlag(start,TOPIC_BLOCKED);
			}
			return NOPROBLEM_BIT;
		}
		int id = FindTopicIDByName(arg2);
		if (!id) return FAILRULE_BIT;
		if (GetTopicFlags(id) & TOPIC_SYSTEM) return FAILRULE_BIT;
		RemoveTopicFlag(id,TOPIC_BLOCKED);
		return NOPROBLEM_BIT;
	}
	else if (!stricmp(ARGUMENT(1),"rule")) 
	{
		if (planning) return FAILRULE_BIT;
		int id = 0;
		unsigned int topic = currentTopicID;
		bool fulllabel;
		bool crosstopic;
		char* rule;
		char* dot = strchr(arg2,'.');
		if (dot && IsDigit(dot[1])) rule = GetRuleTag(topic,id,arg2);
		else rule = GetLabelledRule(topic,arg2,ARGUMENT(3),fulllabel,crosstopic,id,currentTopicID);
		if (!rule) return FAILRULE_BIT;
		UndoErase(rule,topic,id);
		AddTopicFlag(topic,TOPIC_USED); 
		return NOPROBLEM_BIT;
	}
	else if (!stricmp(ARGUMENT(1),"save")) 
	{
		stopUserWrite = false;
		return NOPROBLEM_BIT;
	}
	else if (!stricmp(ARGUMENT(1),"usedrules")) // rules turned off this volley as we went along
	{
		FlushDisabled();
		return NOPROBLEM_BIT;
	}
	else if (!stricmp(ARGUMENT(1),"write")) 
	{
		uint64 set = GetSetID(ARGUMENT(2));
		if (set == ILLEGAL_FACTSET) return FAILRULE_BIT;
		setControl |= (uint64) (1 << set);
		return NOPROBLEM_BIT;
	}
	return FAILRULE_BIT;
}

static FunctionResult LengthCode(char* buffer)
{
	char* word = ARGUMENT(1);
 	if (*word == '@') 
	{
		unsigned int store = GetSetID(word);
		if (store == ILLEGAL_FACTSET) return FAILRULE_BIT;
		unsigned int count = FACTSET_COUNT(store);
		sprintf(buffer,"%d",count);
	}
	else if (*word == '~') // how many top level members in set
	{
		WORDP D = FindWord(word,0);
		if (!D) return FAILRULE_BIT;
		int count = 0;
		FACT* F = GetObjectHead(D);
		while (F)
		{
			if (F->verb == Mmember) ++count;
			F = GetObjectNext(F);
		}
		sprintf(buffer,"%d",count);
	}
	else sprintf(buffer,"%d",(int)strlen(word));
	return NOPROBLEM_BIT;
}

static FunctionResult NextCode(char* buffer)
{
	char word[MAX_WORD_SIZE];
	char* ptr = ReadCompiledWord(ARGUMENT(1),word);
	char* arg1 = ARGUMENT(1); // GAMBIT or RESPONDER or RULE OR FACT or INPUT
	if (!stricmp(word,"FACT")) 
	{
		strcpy(ARGUMENT(1),ptr);
		return FLR(buffer,"n");
	}
	if (!stricmp(word,"INPUT"))
	{
		SAVEOLDCONTEXT()
		*buffer = 0;
		while (ALWAYS) // revise inputs until prepass doesnt change them
		{
			if (!*nextInput) return FAILRULE_BIT;
			PrepareSentence(nextInput,true,true);
			if (!wordCount && (*nextInput | (responseIndex != 0))) // ignore this input
			{
				RESTOREOLDCONTEXT()
				return NOPROBLEM_BIT; 
			}
			if (!PrepassSentence(GetUserVariable("$cs_prepass"))) break; // it was quiet
		}
 		if (!wordCount) return FAILRULE_BIT;
		++inputSentenceCount; //  sentence id of volley has moved on
		RESTOREOLDCONTEXT()
	}
	else  // gambit, responder, rule, REJOINDER
	{
		static char prior[MAX_WORD_SIZE];

		if (*ptr == '~' && !ptr[1]) strcpy(ptr,prior);
		bool gambit = (*arg1 == 'G' || *arg1 == 'g');
		bool responder = !stricmp(arg1,"responder");
		bool rejoinder = !stricmp(arg1,"rejoinder");
		unsigned int topic = currentTopicID;
		int id;
		bool fulllabel = false;
		bool crosstopic = false;
		char* rule;
		char* dot = strchr(ptr,'.');
		if (dot && IsDigit(dot[1])) rule = GetRuleTag(topic,id,ptr);
		else rule = GetLabelledRule(topic,ptr,ARGUMENT(3),fulllabel,crosstopic,id,currentTopicID);
		if (!rule) return FAILRULE_BIT; // unable to find labelled rule 

		char* data = rule;
		while (data)
		{
			data = FindNextRule( (gambit || responder) ? NEXTTOPLEVEL : NEXTRULE,data,id);
			if (!data || !*data) break;
		
			if (gambit && TopLevelGambit(data)) break;
			else if (responder &&  (TopLevelStatement(data) || TopLevelQuestion(data))) break; 
			else if (rejoinder && Rejoinder(data)) break;
			else if (rejoinder) return FAILRULE_BIT;	// no more rejoinders
			else if (!gambit && !responder && !rejoinder) break;	// any next rule
		}
		if (!data || !*data) return FAILRULE_BIT;
		sprintf(buffer,"%s.%d.%d",GetTopicName(topic),TOPLEVELID(id),REJOINDERID(id));
		strcpy(prior,buffer);	// able to iterate easily
	}
	return NOPROBLEM_BIT;
}

static FunctionResult FLRCodeR(char* buffer)
{
	char* word = ARGUMENT(1);
	char arg[MAX_WORD_SIZE];
	ReadCompiledWord(word,arg);
	word = arg;
	if (*word == '^') strcpy(word,callArgumentList[atoi(word+1)+fnVarBase]); // swap to actual

	if (*word == '$') word = GetUserVariable(word);
	else if (*word == '_') word =  GetwildcardText(GetWildcardID(word), true);

	if (*word == '@') return FLR(buffer,"r");
	else if (*word == '~')  return RandomMember(buffer,word);
	else return FAILRULE_BIT;
}

static FunctionResult FLRCodeSpecific(char* buffer)
{
	char* word = ARGUMENT(1);
	char arg[MAX_WORD_SIZE];
	ReadCompiledWord(word,arg);
	char* arg2 = ARGUMENT(2);
	word = arg;
	if (*word == '^') strcpy(word,callArgumentList[atoi(word+1)+fnVarBase]); // swap to actual

	if (*word == '$') word = GetUserVariable(word);
	else if (*word == '_') word =  GetwildcardText(GetWildcardID(word), true);
	else if (*word == '~') // nth member of set, counting from 0
	{
		WORDP D = FindWord(word);
		int n = atoi(arg2);
		FACT* F = GetObjectHead(D);
		int count = 0;
		while (F) // back to front order, need to invert, count how many
		{
			++count;
			F = GetObjectNext(F);
		}
		if (count < n) return FAILRULE_BIT; // not enough or bad count
		F = GetObjectHead(D);
		while (F && --n >= 0) 
			F = GetObjectNext(F); // back to front order, need to invert
		strcpy(buffer,Meaning2Word(F->subject)->word);
		return NOPROBLEM_BIT;
	}
	if (*word == '@') return FLR(buffer,arg2);
	else return FAILRULE_BIT;
}

static FunctionResult ResetCode(char* buffer)
{
	char* word = ARGUMENT(1);
	if (!stricmp(word,"USER"))
	{
		if (planning) return FAILRULE_BIT;
		int depth = globalDepth; // reset clears depth, but we are still in process so need to restore it
		ResetUser(buffer);
		globalDepth = depth;
		StartConversation(buffer);

#ifndef DISCARDTESTING
		wasCommand = COMMANDED;	// lie so system will save revised user file
#endif
		return ENDINPUT_BIT;
	}
	else if (!stricmp(word,"TOPIC"))
	{
		word = ARGUMENT(2);
		unsigned int topic;
		if (*word == '*' && word[1] == 0) // all topics
		{
			if (!all) ResetTopics(); 
		}
		else if ((topic = FindTopicIDByName(word))) ResetTopic(topic);
		else return FAILRULE_BIT;
		return NOPROBLEM_BIT;
	}
	else if (!stricmp(word,"OUTPUT"))
	{
		responseIndex = 0;
		return NOPROBLEM_BIT;
	}
	else if (*word == '@') // reset a fact set for browsing sequentially
	{
		unsigned int store = GetSetID(word);
		if (store == ILLEGAL_FACTSET) return FAILRULE_BIT;
		factSetNext[store] = 0;
		if (trace) Log(STDUSERLOG," @%d[%d] ",store,FACTSET_COUNT(store));
		return NOPROBLEM_BIT;
	}
	return FAILRULE_BIT;
}

//////////////////////////////////////////////////////////
/// EXTERNAL ACCESS
//////////////////////////////////////////////////////////

static FunctionResult ExportFactCode(char* buffer)
{
	char* set = ARGUMENT(2);
	if (*set != '@') return FAILRULE_BIT;
	// optional 3rd argument is append or overwrite
	char* append = ARGUMENT(3);
	return (ExportFacts(ARGUMENT(1),GetSetID(set),append)) ? NOPROBLEM_BIT : FAILRULE_BIT;
}

static FunctionResult ImportFactCode(char* buffer)
{
	return (ImportFacts(ARGUMENT(1),ARGUMENT(2),ARGUMENT(3),ARGUMENT(4))) ? NOPROBLEM_BIT : FAILRULE_BIT;
}

static FunctionResult PopenCode(char* buffer)
{
	char   psBuffer[MAX_WORD_SIZE];
	FILE   *pPipe;
	char* arg;
	arg = ARGUMENT(1);

	// convert \" to " within params
	if (*arg == '"') ++arg;
	size_t len = strlen(arg);
	if (arg[len-1] == '"') arg[len-1] = 0;
	char* fix;
	while ((fix = strchr(arg,'\\'))) memmove(fix,fix+1,strlen(fix)); // remove protective backslash
	
	// adjust function reference name
	char* function = ARGUMENT(2);
	if (*function == '\'') ++function; // skip over the ' 

#ifdef WIN32
   if( (pPipe = _popen(arg,"rb")) == NULL ) return FAILRULE_BIT; //  "dir *.c /on /p", "rt" 
#else
   if( (pPipe = popen(arg,"r")) == NULL ) return FAILRULE_BIT; 
#endif
   psBuffer[0] = '(';
   psBuffer[1] = ' ';
   psBuffer[2] = '"'; // stripable string marker
   psBuffer[3] = ENDUNIT; // stripable string marker
   while( !feof( pPipe ) )
   {
		psBuffer[4] = 0;
		if( fgets( psBuffer+4, MAX_WORD_SIZE - 5, pPipe ) != NULL )
		 {
			FunctionResult result;
			char* p;
			while ((p = strchr(psBuffer,'\r'))) *p = ' ';
			while ((p = strchr(psBuffer,'\n'))) *p = ' ';
			strcat(psBuffer,"`\" )"); // trailing quote and ending paren
			if (*function == '^') DoFunction(function,psBuffer,buffer,result); 
			buffer += strlen(buffer);
			if (result == UNDEFINED_FUNCTION) result = FAILRULE_BIT;
		}
   }
#ifdef WIN32
   _pclose( pPipe );
#else
   pclose( pPipe );
#endif
   return NOPROBLEM_BIT;
}

static FunctionResult TCPOpenCode(char* buffer)
{
#ifdef INFORMATION
// POST http://de.sempar.ims.uni-stuttgart.de/parse HTTP/1.1
// Accept: text/html, application/xhtml+xml, */*
// Host: de.sempar.ims.uni-stuttgart.de
// Content-Type: application/x-www-form-urlencoded
// Content-Length: 31
//
// sentence=ich+bin&returnType=rdf

// e.g.  TCPOpen(POST "http://de.sempar.ims.uni-stuttgart.de/parse" "sentence=ich+bin&returnType=rdf" 'myfunc)
#endif

#ifdef DISCARDTCPOPEN
	char* msg = "tcpopen not available\r\n";
	SetUserVariable("$$tcpopen_error",msg);	// pass along the error
	Log(STDUSERLOG,msg);
	return FAILRULE_BIT;
#else
	size_t len;
	char* url;
	char directory[MAX_WORD_SIZE];
	char* arg;
	char kind = 0;
	FunctionResult result;
	bool encoded = false;
	if (!stricmp(ARGUMENT(1),"POST")) kind = 'P';
	else if (!stricmp(ARGUMENT(1),"GET")) kind = 'G';
	else if (!stricmp(ARGUMENT(1),"POSTU")) 
	{
		kind = 'P';
		encoded = true;
	}
	else if (!stricmp(ARGUMENT(1),"GETU")) 
	{
		kind = 'G';
		encoded = true;
	}
	else 
	{
		char* msg = "tcpopen- only POST and GET allowed\r\n";
		SetUserVariable("$$tcpopen_error",msg);	// pass along the error
		Log(STDUSERLOG,msg);
		return FAILRULE_BIT;
	}

	url = ARGUMENT(2);
	char* dot = strchr(url,'.');
	if (!dot) 
	{
		char* msg = "tcpopen- an url was not given\r\n";
		SetUserVariable("$$tcpopen_error",msg);	// pass along the error
		Log(STDUSERLOG,msg);
		return FAILRULE_BIT;
	}
	char* slash = strchr(dot,'/');
	if (slash) 
	{
		*slash = 0; // leave url as is
		strcpy(directory,slash+1);
	}
	else *directory = 0;

	// convert \" to " within params abd remove any wrapper
	arg = ARGUMENT(3);
	if (*arg == '"') ++arg;
	len = strlen(arg);
	if (arg[len-1] == '"') arg[len-1] = 0;
	char* fix;
	while ((fix = strchr(arg,'\\'))) memmove(fix,fix+1,strlen(fix)); // remove protective backslash

	char originalArg[MAX_WORD_SIZE];
	strcpy(originalArg,arg);

	// url encoding:
	char* ptr = arg - 1;
	if (!encoded) while (*++ptr)
	{
		if (!IsAlphaUTF8(*ptr) && isAlphabeticDigitData[*ptr] != VALIDDIGIT && *ptr != '-'  && *ptr != '_'  && *ptr != '.' && *ptr != '~' && *ptr != '=' && *ptr != '&')
		{
			if (*ptr == ' ')
			{
				*ptr = '+';
				continue;
			}
			memmove(ptr+3,ptr+1,strlen(ptr)); // reserve 2 extra chars
			ptr[1] = toHex[(*ptr >> 4)  & 0x0f];
			ptr[2] = toHex[(*ptr & 0x0f)];
			*ptr = '%';
			ptr += 2;
		}
	}
	
	// adjust function reference name
	char* function = ARGUMENT(4);
	if (*function == '\'') ++function; // skip over the ' 

	unsigned int port = 0;
	if (kind == 'P' || kind == 'G') port = 80;
	else
	{
		char* colon = strchr(url,':');
		if (colon)
		{
			*colon = 0;
			port = atoi(colon+1);
		}
	}
	int size = 0;
	char* tcpbuffer = AllocateBuffer();
	char* startContent = tcpbuffer;
	try 
	{
		if (trace & TRACE_TCP && CheckTopicTrace()) Log(STDUSERLOG,"RAW TCP: %s/%s port:%d %s %s",url,directory,port,(kind == 'G' ) ? (char*)"GET" : (char*) "POST",originalArg);
		TCPSocket *sock = new TCPSocket(url, (unsigned short)port);
		
		if (kind == 'P')
		{
			if (*directory) sprintf(tcpbuffer,"POST /%s HTTP/1.0\r\nHost: %s\r\n",directory,url);
			else sprintf(tcpbuffer,"POST HTTP/1.0\r\nHost: %s\r\n",url);
		}
		else if (kind == 'G') sprintf(tcpbuffer,"GET /%s?%s HTTP/1.0\r\nHost: %s\r\n",directory,arg,url);
		sock->send(tcpbuffer, strlen(tcpbuffer) );
		if (trace & TRACE_TCP && CheckTopicTrace()) Log(STDUSERLOG,"\r\n%s",tcpbuffer);
		
		if (kind == 'P')
		{
			strcpy(tcpbuffer,"Content-Type: application/x-www-form-urlencoded\r\nAccept: text/html, application/xhtml+xml, */*\r\nAccept-Charset: utf-8\r\nUser-Agent: Mozilla/5.0 (compatible; MSIE 10.0; Windows NT 6.2; WOW64; Trident/6.0)\r\n");
			sock->send(tcpbuffer, strlen(tcpbuffer) );
			if (trace & TRACE_TCP && CheckTopicTrace()) Log(STDUSERLOG,"%s",tcpbuffer);
			len = strlen(arg);
			sprintf(tcpbuffer,"Content-Length: %d\r\n\r\n%s\r\n",(unsigned int) len,arg);
		}
		else strcpy(tcpbuffer,"Content-Type: application/x-www-form-urlencoded\r\nAccept: text/html, application/xhtml+xml, */*\r\nAccept-Charset: utf-8\r\nUser-Agent: Mozilla/5.0 (compatible; MSIE 10.0; Windows NT 6.2; WOW64; Trident/6.0)\r\n\r\n"); // GET
		sock->send(tcpbuffer, strlen(tcpbuffer) );
		if (trace & TRACE_TCP && CheckTopicTrace()) Log(STDUSERLOG,"%s",tcpbuffer);
	
		unsigned int bytesReceived = 1;              // Bytes read on each recv()
		unsigned int totalBytesReceived = 0;         // Total bytes read
		char* base = tcpbuffer;
		*base = 0;
		bool hasContent = false;
		int allowedBytes = maxBufferSize - 10;
		while (bytesReceived > 0) 
		{
			// Receive up to the buffer size bytes from the sender
			bytesReceived = sock->recv(base, allowedBytes);
			allowedBytes -= bytesReceived;
			totalBytesReceived += bytesReceived;
			base += bytesReceived;
			if (!hasContent && (kind == 'P' || kind == 'G' ) ) // std POST/GET http formats
			{
				startContent = strstr(tcpbuffer,"\r\n\r\n"); // body separator
				if (!startContent) continue; // not found yet
				startContent += 4;

				char* lenheader = strstr(tcpbuffer,"Content-Length: "); // look for earlier size info
				if (lenheader)
				{
					size = atoi(SkipWhitespace(lenheader+16)); // size of body
					hasContent = true;
				}
			}
			if (hasContent && (base-startContent) >= size) break;	// we have enough
		}
		delete(sock);
		*base++ = 0;
		*base++ = 0;
		// chatbot replies this
		if (trace & TRACE_TCP && CheckTopicTrace()) Log(STDUSERLOG,"tcp received: %d bytes %s",totalBytesReceived,tcpbuffer);
	}
	catch(SocketException e) { 
		char* msg = "tcpopen- failed to connect to server or died in transmission\r\n";
		SetUserVariable("$$tcpopen_error",msg);	// pass along the error
		Log(STDUSERLOG,msg);
		Log(STDUSERLOG,"failed to connect to server %s %d\r\n",url,port); 
		FreeBuffer(); 
		return FAILRULE_BIT;
	}

	// process http return for validity
	if (kind == 'P' || kind == 'G')
	{
		if (strnicmp(tcpbuffer,"HTTP",4)) 
		{
			char* msg = "tcpopen- no HTTP ack code\r\n";
			SetUserVariable("$$tcpopen_error",msg);	
			Log(STDUSERLOG,msg);
			FreeBuffer();
			return FAILRULE_BIT;
		}
		char* space = strchr(tcpbuffer,' ');
		space = SkipWhitespace(space);	// go to end of whitespace
		if (trace & TRACE_TCP && CheckTopicTrace()) Log(STDUSERLOG,"response: %s",space);
		if (*space != '2') 
		{
			char msg[MAX_WORD_SIZE];
			space[5] = 0;
			sprintf(msg,"tcpopen- HTTP ack code bad %s\r\n",space);
			SetUserVariable("$$tcpopen_error",msg);	
			Log(STDUSERLOG,msg);
			FreeBuffer();
			return FAILRULE_BIT;	// failure code of some kind
		}
	}
	
	userRecordSourceBuffer = startContent;
	char* buf1 = AllocateBuffer();
	buf1[0] = '(';
	buf1[1] = ' ';
	buf1[2] = '"'; // strippable string marker
	buf1[3] = ENDUNIT; // strippable string marker
	result = NOPROBLEM_BIT;
	while (result == NOPROBLEM_BIT)
	{
		if (ReadALine(buf1+4,0) < 0) break;
		if (!buf1[4]) continue;		// no content
		char* actual = TrimSpaces(buf1);
		strcat(actual,"`\" )"); // trailing quote and ending paren
		if (*function == '^') DoFunction(function,actual,buffer,result); 
		buffer += strlen(buffer);
		if (result == UNDEFINED_FUNCTION) 
		{
			char* msg = "tcpopen- no such function to call";
			SetUserVariable("$$tcpopen_error",msg);	
			Log(STDUSERLOG,msg);
			result = FAILRULE_BIT;
		}
		else if (result & FAILCODES)
		{
			char* msg = "tcpopen- function call failed";
			SetUserVariable("$$tcpopen_error",msg);	
			Log(STDUSERLOG,msg);
		}
	}
	userRecordSourceBuffer = NULL;
	FreeBuffer();
	FreeBuffer();
	return result;
#endif
}

static FunctionResult SystemCode(char* buffer)
{
	char word[MAX_WORD_SIZE];
	*word = 0;
	char* stream = ARGUMENT(1);
	while (stream && *stream)
	{
		FunctionResult result;
		char name[MAX_WORD_SIZE];
		stream = ReadCommandArg(stream,name,result,OUTPUT_NOQUOTES|OUTPUT_EVALCODE|OUTPUT_NOTREALBUFFER); // name of file
		if (*name)
		{
			strcat(word,name);
			strcat(word," ");
		}
	}
	if (trace & TRACE_OUTPUT && CheckTopicTrace()) Log(STDUSERLOG,"system: %s ",word);
	sprintf(buffer,"%d",system(word));
	if (trace & TRACE_OUTPUT && CheckTopicTrace()) Log(STDUSERLOG," result: %s r\n",buffer);
	return  NOPROBLEM_BIT;
}

//////////////////////////////////////////////////////////
/// FACTS
//////////////////////////////////////////////////////////

static FunctionResult CreateFactCode(char* buffer)
{ 
	currentFact = NULL;
	char* arg = ARGUMENT(1);
	EatFact(arg); // PUTS NOTHING IN THE OUTPUT BUFFER but can be assigned from.
	return (currentFact) ? NOPROBLEM_BIT : FAILRULE_BIT;
}

static FACT* DeleteFromList(FACT* oldlist,FACT* oldfact,GetNextFact getnext,SetNextFact setnext)
{ // olditem can be either a meaning or a factoid. we are lloing for the oldlist fact that has olditem as subject
	FACT* start = oldlist;
	echo = true;
	TraceFact(oldfact);
	TraceFact(oldlist);
	if (oldlist == oldfact) 
	{
		FACT* G = (*getnext)(oldlist);
		TraceFact(G);
		return G;
	}
	FACT* prior = oldlist;
	while (oldlist)
	{
		TraceFact(oldlist);
		FACT* H = (*getnext)(oldlist);
		TraceFact(H);
		if (oldlist == oldfact)
		{
			(*setnext)(prior,H); // remove this from list by skip over
			break;
		}
		prior = oldlist;
		oldlist = H;
	}

	return start;
}

static FACT* AddToList(FACT* newlist,FACT* oldfact,GetNextFact getnext,SetNextFact setnext)
{
	FACT* start = newlist;
	TraceFact(oldfact);
	TraceFact(newlist);
	if (start < oldfact) // we will head the lise
	{
		TraceFact(oldfact);
		(*setnext)(oldfact,newlist);
		return oldfact;
	}
	FACT* prior = newlist;
	while (newlist)
	{
		if (newlist < oldfact) // add fact into list by insert
		{
			(*setnext)(oldfact, newlist);
			(*setnext)(prior, oldfact);
			break;
		}
		prior = newlist;
		newlist = (*getnext)(newlist);
	}
	return start;
}

static void ShowLinks(char* msg,WORDP D,GetNextFact getnext)
{
	echo = 1;
	Log(STDUSERLOG,"%s %s chain: \r\n",msg,D->word);
	FACT* F = GetSubjectHead(D);
	while (F)
	{
		TraceFact(F);
		F = (*getnext)(F);
	}
	Log(STDUSERLOG,"end chain: \r\n");

}

static void ShowFactLinks(char* msg,FACTOID D,GetNextFact getnext)
{
	echo = 1;
	FACT* G = Index2Fact(D);
	TraceFact(G );
	Log(STDUSERLOG,"%s ",msg);
	FACT* F = GetSubjectHead(G );
	while (F)
	{
		TraceFact(F);
		F = (*getnext)(F);
	}
	Log(STDUSERLOG,"end chain: \r\n");
}


static FunctionResult ReviseFactCode(char* buffer)
{ 
	currentFact = NULL;
	char* arg = ARGUMENT(1);
	FACTOID index = atoi(arg);
	FACT* F = Index2Fact(index);
	if (F <= factLocked || F->flags & FACTDEAD) return FAILRULE_BIT; // only user undead facts
	char* subject = ARGUMENT(2);
	char* verb = ARGUMENT(3);
	char* object = ARGUMENT(4);
	if (stricmp(subject,"null"))
	{
		if (F->flags & FACTSUBJECT)
		{
			unsigned int newsubject = atoi(subject); // find the fact replacing it
			FACT* newfact = Index2Fact(index);
			if (!newfact) return FAILRULE_BIT;
			FACTOID oldsubject = F->subject;
			FACT* oldfact = Index2Fact(oldsubject);
			if (index == oldsubject) return NOPROBLEM_BIT;	// no change needed, we accept it
			FACT* X = DeleteFromList(GetSubjectHead(oldfact),F,GetSubjectNext,SetSubjectNext);
			SetSubjectHead(oldfact,X);
			X = AddToList(GetSubjectHead(newfact),F,GetSubjectNext,SetSubjectNext);
			SetSubjectHead(newfact,X);
			F->subject = newsubject;
		}
		else // word replacement
		{
			WORDP oldsubject = Meaning2Word(F->subject);
			WORDP newsubject = StoreWord(subject);
			if (oldsubject == newsubject) return NOPROBLEM_BIT;	// no change needed, we accept it
			FACT* X = DeleteFromList(GetSubjectHead(oldsubject),F,GetSubjectNext,SetSubjectNext);
			SetSubjectHead(oldsubject,X);
			X = AddToList(GetSubjectHead(newsubject),F,GetSubjectNext,SetSubjectNext);
			SetSubjectHead(newsubject,X);
			F->subject = MakeMeaning(newsubject);
		} 
	}
	if (stricmp(verb,"null"))
	{
		if (F->flags & FACTVERB)
		{
			unsigned int newverb = atoi(verb); // find the fact replacing it
			FACT* newfact = Index2Fact(index);
			if (!newfact) return FAILRULE_BIT;
			FACTOID oldverb = F->verb;
			FACT* oldfact = Index2Fact(oldverb);
			if (index == oldverb) return NOPROBLEM_BIT;	// no change needed, we accept it
			FACT* X = DeleteFromList(GetVerbHead(oldfact),F,GetVerbNext,SetVerbNext);
			SetVerbHead(oldfact,X);
			X = AddToList(GetVerbHead(newfact),F,GetVerbNext,SetVerbNext);
			SetVerbHead(newfact,X);
			F->verb = newverb;
		}
		else // word replacement
		{
			WORDP oldverb = Meaning2Word(F->verb);
			WORDP newverb = StoreWord(verb);
			if (oldverb == newverb) return NOPROBLEM_BIT;	// no change needed, we accept it
			FACT* X = DeleteFromList(GetVerbHead(oldverb),F,GetVerbNext,SetVerbNext);
			SetVerbHead(oldverb,X);
			X = AddToList(GetVerbHead(newverb),F,GetVerbNext,SetVerbNext);
			SetVerbHead(newverb,X);
			F->verb = MakeMeaning(newverb);
		} 
	}
	if (stricmp(object,"null"))
	{
		if (F->flags & FACTOBJECT)
		{
			unsigned int newobject = atoi(object); // find the fact replacing it
			FACT* newfact = Index2Fact(index);
			if (!newfact) return FAILRULE_BIT;
			FACTOID oldobject = F->object;
			FACT* oldfact = Index2Fact(oldobject);
			if (index == oldobject) return NOPROBLEM_BIT;	// no change needed, we accept it
			FACT* X = DeleteFromList(GetObjectHead(oldfact),F,GetObjectNext,SetObjectNext);
			SetObjectHead(oldfact,X);
			X = AddToList(GetObjectHead(newfact),F,GetObjectNext,SetObjectNext);
			SetObjectHead(newfact,X);
			F->object = newobject;
		}
		else // word replacement
		{
			WORDP oldobject= Meaning2Word(F->object);
			WORDP newobject = StoreWord(object);
			if (oldobject == newobject) return NOPROBLEM_BIT;	// no change needed, we accept it
			FACT* X = DeleteFromList(GetObjectHead(oldobject),F,GetObjectNext,SetObjectNext);
			SetObjectHead(oldobject,X);
			X = AddToList(GetObjectHead(newobject),F,GetObjectNext,SetObjectNext);
			SetObjectHead(newobject,X);
			F->object = MakeMeaning(newobject);
		} 
	}


#ifdef INFORMATION
	As we create facts, older facts (lower index) will be farther down the list. When we erase a fact, we should be at the top of all xref lists.
#endif
	return NOPROBLEM_BIT;
}

static FunctionResult ConceptListCode(char* buffer)
{
	int set = (impliedSet == ALREADY_HANDLED) ? 0 : impliedSet;
	SET_FACTSET_COUNT(set,0);
	unsigned int how = 0;
	char* arg = ARGUMENT(1);
	char word[MAX_WORD_SIZE];
	arg = ReadCompiledWord(arg,word);
	if (!stricmp(word,"CONCEPT"))
	{
		arg = ReadCompiledWord(arg,word);
		how = 1;
	}
	else if (!stricmp(word,"TOPIC"))
	{
		arg = ReadCompiledWord(arg,word);
		how = 2;
	}
	else if (!stricmp(word,"BOTH"))
	{
		arg = ReadCompiledWord(arg,word);
		how = 3;
	}
	else return FAILRULE_BIT;

	unsigned int start = 1;
	unsigned int end = 1;
	if (*word == '\'') memmove(word,word+1,strlen(word));
	if (*word == '^') strcpy(word,callArgumentList[atoi(word+1)+fnVarBase]); // swap to actual
	
	if (*word == '_') start = end = WildPosition(word);  //  wildcard position designator
	else if (*word == '$') start = end = atoi(GetUserVariable(word));  //  user var
	else if (IsDigit(*word)) start = end = atoi(word);
	else if (!*word) end = wordCount; // overall
	else return FAILRULE_BIT;

	if (start < 1 || start > wordCount) return FAILRULE_BIT;

	char position[MAX_WORD_SIZE];
	unsigned int list;
	for (unsigned int i = start; i <= end; ++i)
	{
		sprintf(position,"%d",i);
		if (how & 1)
		{
			list = concepts[i];
			while (list)
			{
				MEANING* at = (MEANING*)Index2String(list);
				WORDP X = Meaning2Word(*at);
				if (!(X->systemFlags & NOCONCEPTLIST)) 
				{
					FACT* base = factFree;
					FACT* F = CreateFact(*at,Mconceptlist,MakeMeaning(StoreWord(position)),FACTTRANSIENT);
					if (F != base) AddFact(set,F);
				}
				list = (unsigned int) at[1];
			}
		}
		if (how & 2)
		{
			list = topics[i];
			while (list)
			{
				MEANING* at = (MEANING*)Index2String(list);
				WORDP X = Meaning2Word(*at);
				if (!(X->systemFlags & NOCONCEPTLIST)) 
				{
					FACT* base = factFree;
					FACT* F = CreateFact(*at,Mconceptlist,MakeMeaning(StoreWord(position)),FACTTRANSIENT);
					if (F != base) AddFact(set,F);
				}
				list = (unsigned int) at[1];
			}
		}
	}
	if (impliedSet == ALREADY_HANDLED && FACTSET_COUNT(set) == 0) return FAILRULE_BIT;
	impliedSet = ALREADY_HANDLED;

	return NOPROBLEM_BIT;
}

static FunctionResult CreateAttributeCode(char* buffer)
{ 
	currentFact = NULL;
	EatFact(ARGUMENT(1),0,true);
	if (currentFact && !(currentFact->flags & FACTATTRIBUTE)) return FAILINPUT_BIT;	// kill the whole line.
	return (currentFact) ? NOPROBLEM_BIT : FAILRULE_BIT; // fails if pre-existing fact cant be killed because used in fact
}

static FunctionResult DeleteCode(char* buffer) //   delete all facts in collection
{
	char* arg1 = ARGUMENT(1);
	if (IsDigit(*arg1))
	{
		FACT* F = Index2Fact(atoi(arg1));
		if (F) KillFact(F);
	}
	else
	{
		int store = GetSetID(ARGUMENT(1));
		if (store == ILLEGAL_FACTSET) return FAILRULE_BIT;
		unsigned int count = FACTSET_COUNT(store);
		for (unsigned int i = 1; i <= count; ++i) KillFact(factSet[store][i]);
	}
	return NOPROBLEM_BIT;
}

static FunctionResult FlushFactsCode(char* buffer) // delete all facts after this one (presuming sentence failed)
{
	if (planning) return FAILRULE_BIT; // dont allow this in planner

	unsigned int f = atoi(ARGUMENT(1)); 
	FACT* F = factFree;
	if (f > Fact2Index(F)) return FAILRULE_BIT;
	while (Fact2Index(F) > f)
	{
		F->flags |= FACTDEAD;	// kill it. dont have to do it recursive (KillFact) because everything that might be using this is already killed by this loop
		--F;
	}
	return NOPROBLEM_BIT;
}

static FunctionResult FieldCode(char* buffer) 
{	
	FACT* F;
	char* word = ARGUMENT(1);
	char word1[MAX_WORD_SIZE];
	if (*word == '@') return FAILRULE_BIT;
	F = FactTextIndex2Fact(word); 
	if (!F || F > factFree) return FAILRULE_BIT;

	WORDP xxs = Meaning2Word(F->subject); // for debugging
	WORDP xxv = Meaning2Word(F->verb);  // for debugging
	WORDP xxo = Meaning2Word(F->object);  // for debugging
	char* arg2 = ARGUMENT(2);
	if (*arg2 == 's' || *arg2 == 'S') 
	{
		if (F->flags & FACTSUBJECT) 
		{
			if (*arg2 == 's') sprintf(buffer,"%d",F->subject);
			else strcpy(buffer,WriteFact(Index2Fact(F->subject),false,word1,false,false));
		}
		else strcpy(buffer,WriteMeaning(F->subject));
	}
	else if (*arg2 == 'v' || *arg2 == 'V') 
	{
		if (F->flags & FACTVERB) 
		{
			if (*arg2 == 'v') sprintf(buffer,"%d",F->verb);
			else strcpy(buffer,WriteFact(Index2Fact(F->verb),false,word1,false,false));
		}
		else strcpy(buffer,WriteMeaning(F->verb));
	}
	else if (*arg2 == 'o' || *arg2 == 'O') 
	{
		if (F->flags & FACTOBJECT) 
		{
			if (*arg2 == 'o') sprintf(buffer,"%d",F->object);
			else strcpy(buffer,WriteFact(Index2Fact(F->object),false,word1,false,false));
		}
		else strcpy(buffer,WriteMeaning(F->object));
	}
	else if (*arg2 == 'f' || *arg2 == 'f') 
	{
		sprintf(buffer,"%d",F->flags);
	}
	else if (*arg2 == 'a' || *arg2 == 'A') // all
	{
		char word[MAX_WORD_SIZE];
		if (impliedWild == ALREADY_HANDLED)  return FAILRULE_BIT;	// must spread them
		SetWildCardIndexStart(impliedWild); //   start of wildcards to spawn
		if (F->flags & FACTSUBJECT)  sprintf(word,"%d",F->subject);
		else  strcpy(word,Meaning2Word(F->subject)->word);
		if (trace & TRACE_INFER && CheckTopicTrace()) Log(STDUSERLOG," _%d = %s ",impliedWild,word);
		SetWildCard(word,word,0,0);
		if (F->flags & FACTVERB)  sprintf(word,"%d",F->verb);
		else  strcpy(word,Meaning2Word(F->verb)->word);
		if (trace & TRACE_INFER && CheckTopicTrace()) Log(STDUSERLOG," _%d = %s ",impliedWild+1,word);
		SetWildCard(word,word,0,0);
		if (F->flags & FACTOBJECT)  sprintf(word,"%d",F->object);
		else  strcpy(word,Meaning2Word(F->object)->word);
		if (trace & TRACE_INFER && CheckTopicTrace()) Log(STDUSERLOG," _%d = %s ",impliedWild+2,word);
		SetWildCard(word,word,0,0);
		impliedWild = ALREADY_HANDLED;	//   we did the assignment
	}
	else if (*arg2 == 'r' || *arg2 == 'R') // all raw
	{
		char word[MAX_WORD_SIZE];
		if (impliedWild == ALREADY_HANDLED)  return FAILRULE_BIT;	// must spread them
		SetWildCardIndexStart(impliedWild); //   start of wildcards to spawn
		if (F->flags & FACTSUBJECT)  sprintf(word,"%d",F->subject);
		else  strcpy(word,WriteMeaning(F->subject));
		if (trace & TRACE_INFER && CheckTopicTrace()) Log(STDUSERLOG," _%d = %s ",impliedWild,word);
		SetWildCard(word,word,0,0);
		if (F->flags & FACTVERB)  sprintf(word,"%d",F->verb);
		else  strcpy(word,WriteMeaning(F->verb));
		if (trace & TRACE_INFER && CheckTopicTrace()) Log(STDUSERLOG," _%d = %s ",impliedWild+1,word);
		SetWildCard(word,word,0,0);
		if (F->flags & FACTOBJECT)  sprintf(word,"%d",F->object);
		else  strcpy(word,WriteMeaning(F->object));
		if (trace & TRACE_INFER && CheckTopicTrace()) Log(STDUSERLOG," _%d = %s ",impliedWild+2,word);
		SetWildCard(word,word,0,0);
		impliedWild = ALREADY_HANDLED;	//   we did the assignment
	}
	else return FAILRULE_BIT;
	return NOPROBLEM_BIT;
}

static FunctionResult FindCode(char* buffer) // given a set, find the ordered position of the 2nd argument in it 
{   
	char word[MAX_WORD_SIZE];
	char* arg1 = ARGUMENT(1); // set
	char* arg2 = ARGUMENT(2); // item
	strcpy(word,JoinWords(BurstWord(arg2),false)); //  the value to find
	WORDP D = FindWord(arg1);
	if (*arg1 == '@')
	{
		FACT* F = Index2Fact(atoi(arg2));
		unsigned int set = GetSetID(arg1);
		if (set == ILLEGAL_FACTSET) return FAILRULE_BIT;
		unsigned int count =  FACTSET_COUNT(set);
		for (unsigned int i = 1; i <= count; ++i)
		{
			if (F == factSet[set][i]) 
			{
				sprintf(buffer,"%d",i);
				return NOPROBLEM_BIT;
			}
		}
		return FAILRULE_BIT;
	}
	else if (D && *arg1 == '~')
	{
		int n = -1;
		FACT* F = GetObjectHead(D);  
		while (F ) // walks set MOST recent (right to left)
		{
			if (F->verb == Mmember) 
			{
				++n;
				WORDP item = Meaning2Word(F->subject);
				if (!stricmp(item->word,word))
				{
					sprintf(buffer,"%d",n);
					return NOPROBLEM_BIT;
				}
			}
			F = GetObjectNext(F);
		}
	}

	return FAILRULE_BIT; 
}

static FunctionResult FindFactCode(char* buffer) // given a Simple fact
{   
	char* arg1 = ARGUMENT(1);
	char* arg2 = ARGUMENT(2);
	char* arg3 = ARGUMENT(3);
	FACT* F = FindFact(ReadMeaning(arg1,false),ReadMeaning(arg2,false),ReadMeaning(arg3,false),0); 
	if (!F) return FAILRULE_BIT;
	sprintf(buffer,"%d",Fact2Index(F));
	return NOPROBLEM_BIT;
}

static FACT* FindF(MEANING subject,WORDP verb,uint64 marker)
{ 
	FACT* F = GetSubjectHead(subject);
    while (F)
    {
		WORDP v = Meaning2Word(F->verb);
        if (v == verb) 
		{
			WORDP obj = Meaning2Word(F->object);
			if (marker != MARKED_WORD) // using a fact marking for find
			{
				if (F->flags & marker) return F;
			}
			else if (obj->systemFlags & marker) return F; // can use marked word flag as well
			FACT* G = FindF(F->object,verb,marker);
			if (G) return G;
		}
        F = GetSubjectNext(F);
    }

	return 0;
}

static FunctionResult FindMarkedFactCode(char* buffer)
{ 
	WORDP subject = FindWord(ARGUMENT(1));
	if (!subject) return FAILRULE_BIT;
	WORDP verb = FindWord(ARGUMENT(2));
	if (!verb) return FAILRULE_BIT;
	char* mark = ARGUMENT(3);
	int64 marker;
	if (IsDigit(*mark)) ReadInt64(mark,marker);
	else marker = FindValueByName(mark); // a fact marker like MARKED_FACT  or word systemflag marker like MARKED_WORD
	if (!marker) return FAILRULE_BIT;

	FACT* F = FindF(MakeMeaning(subject),verb,marker);
	if (trace & TRACE_INFER && CheckTopicTrace()) 
	{
		if (F) 
		{
			Log(STDUSERLOG,"FindMarkedFact found ");
			TraceFact(F);
		}
		else Log(STDUSERLOG,"FindMarkedFact not found ");
	}
	if (!F) return FAILRULE_BIT;

	sprintf(buffer,"%d",Fact2Index(F)); // return index
	return NOPROBLEM_BIT;
}

static FunctionResult FLRCodeF(char* buffer)
{
	return FLR(buffer,"f");
}

static FunctionResult IntersectFactsCode(char* buffer) 
{      
	char* word = ARGUMENT(1);
	char from[MAX_WORD_SIZE];
	char to[MAX_WORD_SIZE];
	FunctionResult result;
	word = ReadShortCommandArg(word,from,result,OUTPUT_KEEPQUERYSET|OUTPUT_NOTREALBUFFER);
	word = ReadShortCommandArg(word,to,result,OUTPUT_KEEPQUERYSET|OUTPUT_NOTREALBUFFER);
	unsigned int store = (impliedSet == ALREADY_HANDLED) ? 0 : impliedSet;
    SET_FACTSET_COUNT(store,0);

    WORDP D;
    FACT* F;
    unsigned int usedMark = NextInferMark();
    unsigned int i;
	char toKind = 's';
	unsigned int where = GetSetID(from); 
	if (where == ILLEGAL_FACTSET) return FAILRULE_BIT;

	if (*to != '@') // mark word
	{
		D = FindWord(to);
		if (D) D->inferMark = usedMark;
	}
	else //  mark set
	{
		unsigned toset = GetSetID(to);
		if (toset == ILLEGAL_FACTSET) return FAILRULE_BIT;
		toKind = GetLowercaseData(*GetSetType(to)); // s v o null
		unsigned int limit = FACTSET_COUNT(toset);
		for (i = 1; i <= limit; ++i)
		{
			WORDP D;
			F = factSet[toset][i];
			if (!F) continue;
			if (trace & TRACE_INFER && CheckTopicTrace())   TraceFact(F);
			if (toKind == 's') Meaning2Word(F->subject)->inferMark = usedMark;
 			else if (toKind == 'v') Meaning2Word(F->verb)->inferMark = usedMark;
 			else if (toKind == 'o') Meaning2Word(F->object)->inferMark = usedMark;
			else // mark all pieces
			{
				D = Meaning2Word(F->subject);
				D->inferMark = usedMark;
				D = Meaning2Word(F->verb);
				D->inferMark = usedMark;
				D = Meaning2Word(F->object);
				D->inferMark = usedMark;
				F->flags |= MARKED_FACT;
			}
		}
	}

    // look for matches
	char fromKind = GetLowercaseData(*GetSetType(from)); // s v o null
    unsigned int limit = FACTSET_COUNT(where);
  	if (trace & TRACE_INFER) Log(STDUSERLOG," // ");
	for (i = 1; i <= limit; ++i)
    {
        F = factSet[where][i];
		if (!F) continue;
 		if (trace & TRACE_INFER && CheckTopicTrace())   TraceFact(F);
 		if (fromKind == 's' && Meaning2Word(F->subject)->inferMark == usedMark) AddFact(store,F);
 		else if (fromKind == 'v' && Meaning2Word(F->verb)->inferMark == usedMark) AddFact(store,F);
		else if (fromKind == 'o' && Meaning2Word(F->object)->inferMark == usedMark) AddFact(store,F);
		else 
		{
			// entire fact found
			if (toKind != 's' && toKind != 'v' && toKind != 'o' &&  F->flags & MARKED_FACT) AddFact(store,F);
			// some piece found
			else if (Meaning2Word(F->subject)->inferMark == usedMark || Meaning2Word(F->verb)->inferMark == usedMark || Meaning2Word(F->object)->inferMark == usedMark) AddFact(store,F);
		}
    }
 	unsigned int count = FACTSET_COUNT(store);
	if (trace & TRACE_INFER && CheckTopicTrace())
	{
		Log(STDUSERLOG,"Found %d in IntersectFact\r\n",count);
		for (i = 1; i <= count; ++i) TraceFact(factSet[store][i]);
	}
	if (impliedSet == ALREADY_HANDLED && !count) return FAILRULE_BIT;
	impliedSet = ALREADY_HANDLED;
    return NOPROBLEM_BIT;
}

static FunctionResult UniqueFactsCode(char* buffer) 
{      
	char* word = ARGUMENT(1);
	char from[MAX_WORD_SIZE];
	char to[MAX_WORD_SIZE];
	FunctionResult result;
	word = ReadShortCommandArg(word,from,result,OUTPUT_KEEPQUERYSET|OUTPUT_NOTREALBUFFER);
	word = ReadShortCommandArg(word,to,result,OUTPUT_KEEPQUERYSET|OUTPUT_NOTREALBUFFER);
	unsigned int store = (impliedSet == ALREADY_HANDLED) ? 0 : impliedSet;
    SET_FACTSET_COUNT(store,0);

    WORDP D;
    FACT* F;
    unsigned int usedMark = NextInferMark();
    unsigned int i;
	char toKind = 's';
	unsigned int where = GetSetID(from); 
	if (where == ILLEGAL_FACTSET) return FAILRULE_BIT;

	if (*to != '@') // mark word
	{
		D = FindWord(to);
		if (D) D->inferMark = usedMark;
	}
	else //  mark set
	{
		unsigned toset = GetSetID(to);
		if (toset == ILLEGAL_FACTSET) return FAILRULE_BIT;
		toKind = GetLowercaseData(*GetSetType(to)); // s v o null
		unsigned int limit = FACTSET_COUNT(toset);
		for (i = 1; i <= limit; ++i)
		{
			WORDP D;
			F = factSet[toset][i];
			if (!F) continue;
			if (trace & TRACE_INFER && CheckTopicTrace())   TraceFact(F);
			if (toKind == 's') Meaning2Word(F->subject)->inferMark = usedMark;
 			else if (toKind == 'v') Meaning2Word(F->verb)->inferMark = usedMark;
 			else if (toKind == 'o') Meaning2Word(F->object)->inferMark = usedMark;
			else // mark all pieces
			{
				D = Meaning2Word(F->subject);
				D->inferMark = usedMark;
				D = Meaning2Word(F->verb);
				D->inferMark = usedMark;
				D = Meaning2Word(F->object);
				D->inferMark = usedMark;
				F->flags |= MARKED_FACT;
			}
		}
	}

    // look for non matches
	char fromKind = GetLowercaseData(*GetSetType(from)); // s v o null
    unsigned int limit = FACTSET_COUNT(where);
  	if (trace & TRACE_INFER && CheckTopicTrace()) Log(STDUSERLOG," // ");
	for (i = 1; i <= limit; ++i)
    {
        F = factSet[where][i];
		if (!F) continue;
 		if (trace & TRACE_INFER && CheckTopicTrace())   TraceFact(F);
 		if (fromKind == 's' && Meaning2Word(F->subject)->inferMark != usedMark) AddFact(store,F);
 		else if (fromKind == 'v' && Meaning2Word(F->verb)->inferMark != usedMark) AddFact(store,F);
		else if (fromKind == 'o' && Meaning2Word(F->object)->inferMark != usedMark) AddFact(store,F);
		else 
		{
			// entire fact not found
			if (toKind != 's' && toKind != 'v' && toKind != 'o' &&  !(F->flags & MARKED_FACT)) AddFact(store,F);
			// some piece found
			else if (Meaning2Word(F->subject)->inferMark != usedMark && Meaning2Word(F->verb)->inferMark != usedMark && Meaning2Word(F->object)->inferMark != usedMark) AddFact(store,F);
		}
    }
 	unsigned int count = FACTSET_COUNT(store);
	if (trace & TRACE_INFER && CheckTopicTrace())
	{
		Log(STDUSERLOG,"Found %d in UniqueFact\r\n",count);
		for (i = 1; i <= count; ++i) TraceFact(factSet[store][i]);
	}
	if (impliedSet == ALREADY_HANDLED && !count) return FAILRULE_BIT;
	impliedSet = ALREADY_HANDLED;
    return NOPROBLEM_BIT;
}

static FunctionResult IteratorCode(char* buffer)
{// ? is std iterator ?? is recursive
	char* arg1 = ARGUMENT(1);
	char* arg2 = ARGUMENT(2);
	char* arg3 = ARGUMENT(3);
	WORDP verb = FindWord(arg2);
	if (!verb) return FAILRULE_BIT;
	MEANING v = MakeMeaning(verb);
	FACT* F;
	WORDP D;
	FACT* holdIterator = NULL;
	if (currentIterator) // this is a return to iteration- either a normal fact or a special fact containing both hieararcy and normal fact data
	{
		F = Index2Fact(currentIterator);
		if (F->flags & ITERATOR_FACT) 
		{
			holdIterator = F;
			F = Index2Fact(F->object);
		}
		F = (*arg1 == '?') ?  GetObjectNext(F) : GetSubjectNext(F);
	}
	else // this is a start of iteration
	{
		if (*arg1 == '?') 
		{
			D = FindWord(arg3); // simple word, not meaning
			F = (D) ? GetObjectHead(D) : NULL;
		}
		else
		{
			D = FindWord(arg1); // simple word, not meaning
			F = (D) ? GetSubjectHead(D) : NULL;
		}
	}
	retry: // level return if any
	while (F)
	{
		if (F->verb == v)
		{
			if (arg1[1] == '?' || arg3[1] == '?') // recursive on concepts?
			{
				MEANING field = (*arg1 == '?') ? F->subject : F->object;
				WORDP E = Meaning2Word(field);
				if (*E->word == '~') // going to nest within
				{
					FACT* G = SpecialFact(holdIterator ? (holdIterator->verb) : 0,Fact2Index(F),ITERATOR_FACT); // remember where we were
					F = (*arg1 == '?') ? GetObjectHead(E) : GetSubjectHead(E);
					if (!holdIterator) holdIterator = SpecialFact(Fact2Index(G),Fact2Index(F),ITERATOR_FACT); // we return this as holding current level and prior level tree
					else holdIterator->verb = Fact2Index(G);
					continue;	// resume hunting at lower level
				}
			}
			break; // found one
		}
		F = (*arg1 == '?') ?  GetObjectNext(F) : GetSubjectNext(F);
	}
	if (!F) // ran dry
	{
		if (holdIterator) // back out of recursive on concepts?
		{
			F = Index2Fact(holdIterator->verb);  // this is a special fact also
			if (!F) return FAILRULE_BIT;		// levels ran dry
			holdIterator->verb = F->verb;		// hold now points higher
			F = Index2Fact(F->object);			// where we were at the higher level
			F = (*arg1 == '?') ?  GetObjectNext(F) : GetSubjectNext(F);
			goto retry;
		}
		return FAILRULE_BIT;
	}
	MEANING M = (*arg1 == '?') ? F->subject : F->object;
	sprintf(buffer,"%s",WriteMeaning(M));
	if (!withinLoop && planning && !backtrackable) backtrackable = true;

	if (holdIterator)
	{
		holdIterator->object = Fact2Index(F); // alter we are pair of hierarchy return and current
		F = holdIterator;
	}
	currentIterator = Fact2Index(F); 
	return NOPROBLEM_BIT;
}

static FunctionResult MakeRealCode(char* buffer)
{
	FACT* at = factFree+1;
	while (--at > factLocked) // user facts
	{
		if (at->flags & FACTTRANSIENT) at->flags ^= FACTTRANSIENT;
	}
	
	return NOPROBLEM_BIT;
}

static FunctionResult FLRCodeL(char* buffer)
{
	return FLR(buffer,"l");
}
extern int backtrackIndex;
static FunctionResult QueryCode(char* buffer)
{ //   kind, s, v, o, count,  from, to, propogate, mark 
	unsigned int count = 0;
	char* ptr = ARGUMENT(1);
	int argcount = 0;
	while (ptr && *ptr) // break apart arguments, but leave any quoted arg UNEVALED.
	{
		argcount++;
		char word[MAX_WORD_SIZE];
		ptr = ReadCompiledWord(ptr,word);
		if (*word != '\'')
		{
			FunctionResult result = NOPROBLEM_BIT;
			ReadShortCommandArg(word,ARGUMENT(argcount),result);
			if (result != NOPROBLEM_BIT) return result;
		}
		else strcpy(ARGUMENT(argcount),word);
	}

	for (unsigned int i = argcount+1; i <= 9; ++i) strcpy(ARGUMENT(i),""); // default rest of args to ""
	if (IsDigit(ARGUMENT(5)[0])) ReadInt(ARGUMENT(5),count); // defaults to ? if not given
	if (count == 0) count = (unsigned int) -1; // infinite

	if (argcount < 9) while (++argcount <= 9) strcpy(ARGUMENT(argcount),"?"); //   default rest of calling Arguments
	char set[50];
	char* arg1 = ARGUMENT(1);
	char* subject = ARGUMENT(2);
	char* verb = ARGUMENT(3);
	char* object = ARGUMENT(4);
	char* from = ARGUMENT(6);
	char* to = ARGUMENT(7);
	char* arg8 = ARGUMENT(8);
	char* arg9 = ARGUMENT(9);

	if (impliedSet != ALREADY_HANDLED) 
	{
		sprintf(set,"@%d",impliedSet); 
		to = set;
	}
	count = Query(arg1, subject, verb, object, count, from, to,arg8, arg9);
	
	// result was a count. now convert to a fail code
	FunctionResult result;
	if (impliedSet != ALREADY_HANDLED) result = NOPROBLEM_BIT;
	else result = (count != 0) ? NOPROBLEM_BIT : FAILRULE_BIT; 
	impliedSet = ALREADY_HANDLED;
	return result;
}

static FunctionResult SortCode(char* buffer) // sorts low to high
{
	char* arg = ARGUMENT(1); // stream
	char word[MAX_WORD_SIZE];
	arg = SkipWhitespace(ReadCompiledWord(arg,word));
	if (*word != '@') return FAILRULE_BIT;	
    unsigned int n = GetSetID(word);
	if (n == ILLEGAL_FACTSET) return FAILRULE_BIT;
	unsigned int count = FACTSET_COUNT(n);
	bool multiple = false;
	// if chained sets, number the facts of the original
	if (*arg == '@')
	{
		// verify they all have the same count
		char* at = arg;
		while (*at == '@') // sort the others to correspond
		{
			at = SkipWhitespace(ReadCompiledWord(at,word));
			unsigned int a = GetSetID(word);
			if (a == ILLEGAL_FACTSET) return FAILRULE_BIT;
			if (FACTSET_COUNT(a) != count) return FAILRULE_BIT;
		}

		multiple = true;
		if (count > 0x0000ffff) return FAILRULE_BIT;	// too many facts to count
		for (unsigned int i = 1; i <= count; ++i)
		{
			FACT* F = factSet[n][i];
			if (F) F->flags |= (i << 16);
		}
	}

	SortFacts(word); // sort the original

	while (*arg == '@') // sort the others to correspond
	{
		arg = SkipWhitespace(ReadCompiledWord(arg,word));
		unsigned int a = GetSetID(word);
		memcpy(&factSet[20],&factSet[a],sizeof(FACT*) *  (FACTSET_COUNT(a) + 1)); // duplicate it
		for (unsigned int i = 1; i <= count; ++i)
		{
			if (!factSet[n]) continue;
			unsigned int index = factSet[n][i]->flags >> 16;	// the new index at this position
			factSet[a][i] = factSet[20][index];
		}
	}

	// if chained sets, unmark the original facts
	if (multiple)
	{
		for (unsigned int i = 1; i <= count; ++i)
		{
			FACT* F = factSet[n][i];
			if (F) F->flags &= 0x0000ffff;
		}
		SET_FACTSET_COUNT(20,0); // remove junk data
	}

	return NOPROBLEM_BIT;
}

static FunctionResult UnduplicateCode(char* buffer)
{
	if (impliedSet == ALREADY_HANDLED) return FAILRULE_BIT;

	int from = GetSetID(ARGUMENT(1));
	if (from == ILLEGAL_FACTSET) return FAILRULE_BIT;
	if (impliedSet == from) return FAILRULE_BIT; // cant do in-place
	unsigned int count = FACTSET_COUNT(from);
	SET_FACTSET_COUNT(impliedSet,0);

	// copy unmarked facts to to
	unsigned int i;
	for (i = 1; i <= count; ++i) 
	{
		FACT* F = factSet[from][i];
		if (!F) continue;
		if (!(F->flags & MARKED_FACT))
		{
			AddFact(impliedSet,F);
			F->flags |= MARKED_FACT;
		}
	}

	// erase marks
	count = FACTSET_COUNT(impliedSet);
	for (i = 1; i <= count; ++i) factSet[impliedSet][i]->flags ^= MARKED_FACT;

	if (trace & TRACE_INFER && CheckTopicTrace()) Log(STDUSERLOG,"Unduplicated %d entries\r\n",count);
	impliedSet = ALREADY_HANDLED;
	return NOPROBLEM_BIT;
}

static FunctionResult UnpackFactRefCode(char* buffer)
{
	if (impliedSet == ALREADY_HANDLED) return FAILRULE_BIT;
	char* arg1 = ARGUMENT(1);
	int from = GetSetID(arg1);
	if (from == ILLEGAL_FACTSET) return FAILRULE_BIT;
	int count = FACTSET_COUNT(from);
	char* type = GetSetType(arg1);
	SET_FACTSET_COUNT(impliedSet,0);
	FACT* G;
	for (int i = 1; i <= count; ++i)
	{
		FACT* F = factSet[from][i];
		if (!F) continue;
		if (F->flags & FACTSUBJECT && *type != 'v' && *type != 'o') 
		{
			G = Index2Fact(F->subject);
			if (trace & TRACE_INFER && CheckTopicTrace()) TraceFact(G);
			AddFact(impliedSet,G);
		}
		if (F->flags & FACTVERB && *type != 's' && *type != 'o') 
		{
			G = Index2Fact(F->verb);
			if (trace & TRACE_INFER && CheckTopicTrace()) TraceFact(G);
			AddFact(impliedSet,G);
		}
		if (F->flags & FACTOBJECT && *type != 's' && *type != 'v') 
		{
			 G = Index2Fact(F->object);
			if (trace & TRACE_INFER && CheckTopicTrace()) TraceFact(G);
			AddFact(impliedSet,G);
		}
	}
	impliedSet = ALREADY_HANDLED;
	return NOPROBLEM_BIT;
}

SystemFunctionInfo systemFunctionSet[] =
{
	{"",0,0,0,""},

	{"\r\n---- Topic",0,0,0,""},
	{"^addtopic",AddTopicCode,1,SAMELINE,"note a topic as interesting"}, //O
	{"^available",AvailableCode,VARIABLE_ARG_COUNT,0,"is rule still available or has it been disabled"}, 
	{"^cleartopics",ClearTopicsCode,0,SAMELINE,"remove all interesting topics in queue"},
	{"^counttopic",CountTopicCode,2,SAMELINE,"provide topic and count requested: GAMBIT, AVAILABLE, RULE, USED"}, 
	{"^gambit",GambitCode,VARIABLE_ARG_COUNT,0,"execute topic in gambit mode, naming ~ ~topicname PENDING or keyword"}, 
	{"^getverify",GetVerifyCode,1,0,""}, 
	{"^getrule",GetRuleCode,VARIABLE_ARG_COUNT,0,"get the requested data (TAG,TYPE,LABEL,PATTERN,OUTPUT,TOPIC,USABLE) for rule tag or label"},
	{"^topicflags",TopicFlagsCode,1,SAMELINE,"Get topic control bits"}, 
	{"^lastused",LastUsedCode,2,SAMELINE,"Get input count of last topic access - GAMBIT, RESPONDER, REJOINDER, ANY"}, 
	{"^hasgambit",HasGambitCode,VARIABLE_ARG_COUNT,0,"name of topic to test for an unexpired gambit, LAST/ANY/"}, 
	{"^keep",KeepCode,0,SAMELINE,"do not erase rule after use"}, 
	{"^poptopic",PopTopicCode,VARIABLE_ARG_COUNT,0,"remove current or named topic from interesting set"}, 
	{"^refine",RefineCode,VARIABLE_ARG_COUNT,0,"execute continuations until one matches"}, 
	{"^rejoinder",RejoinderCode,VARIABLE_ARG_COUNT,0,"try to match a pending rejoinder - not legal in postprocessing"}, 
	{"^respond",RespondCode,VARIABLE_ARG_COUNT,0,"execute a topic's responders"}, 
	{"^reuse",ReuseCode,VARIABLE_ARG_COUNT,0,"jump to a rule label or tag and execute output section"}, 
	{"^setrejoinder",SetRejoinderCode,VARIABLE_ARG_COUNT,0,"Set rejoinder {INPUT OUTPUT} mark to this tag"}, 

	{"\r\n---- Topic Lists",0,0,0,""},
	{"^gambittopics",GetTopicsWithGambitsCode,0,0,"get all topics that have usable gambits that are not current topic"}, 
	{"^keywordtopics",KeywordTopicsCode,VARIABLE_ARG_COUNT,0,"get facts of topics that cover keywords mentioned in input"}, 
	{"^pendingtopics",PendingTopicsCode,1,0,"return list of currently pending topics as facts in 1st arg"}, 
	{"^querytopics",QueryTopicsCode,1,0,"get topics of which 1st arg is a keyword?"}, 

	{"\r\n---- Marking & Parser Info",0,0,0,""},
	{"^mark",MarkCode,STREAM_ARG,SAMELINE,"mark word/concept in sentence"},
	{"^marked",MarkedCode,1,SAMELINE,"BOOLEAN - is word/concept marked in sentence"}, 
	{"^position",PositionCode,STREAM_ARG,SAMELINE,"get FIRST or LAST position of an _ var"}, 
	{"^setposition",SetPositionCode,STREAM_ARG,SAMELINE,"set absolute match position"}, 
	{"^setpronoun",SetPronounCode,STREAM_ARG,SAMELINE,"replace pronoun with word"}, 
	{"^unmark",UnmarkCode,STREAM_ARG,SAMELINE,"remove a mark on a word/concept in the sentence"}, 

	{"\r\n---- Input",0,0,0,""},
	{"^getparse",GetParseCode,2,SAMELINE,"[POS,ROLE,LINK] matchvar"}, 
	{"^analyze",AnalyzeCode,STREAM_ARG,0,"Take an output stream and do preparation on it like it was user input"}, 
	{"^capitalized",CapitalizedCode,1,SAMELINE,"given index of word in sentence return 1 or 0 for whether user capitalized it"}, 
	{"^decodepos",DecodePosCode,2,SAMELINE,"decode into text the pos bits of given pos (POS) or role (ROLE) "}, 
	{"^input",InputCode,STREAM_ARG,0,"submit stream as input immediately after current input"},
	{"^partofspeech",PartOfSpeechCode,STREAM_ARG,SAMELINE,"given index of word in sentence return 64-bit pos data from parsing"}, 
	{"^phrase",PhraseCode,STREAM_ARG,0,"get noun or prep phrase at location, possibly canonical"},
	{"^removetokenflags",RemoveTokenFlagsCode,1,SAMELINE,"remove value from tokenflags"}, 
	{"^role",RoleCode,STREAM_ARG,SAMELINE,"given index of word in sentence return 32-bit role data from parsing"}, 
	{"^settokenflags",SetTokenFlagsCode,1,SAMELINE,"add value to tokenflags"}, 
	{"^setwildcardindex",SetWildcardIndexCode,STREAM_ARG,SAMELINE,"resume wildcard allocation at this number"}, 

	{"\r\n---- Numbers",0,0,0,""},
	{"^compute",ComputeCode,3,SAMELINE,"perform a numerical computation"}, 
	{"^isnumber",IsNumberCode,1,SAMELINE,"is this an integer or float number or currency"}, 
	{"^timefromseconds",TimeFromSecondsCode,1,SAMELINE,"given time/date in seconds, return the timeinfo string corresponding to it"}, 
	{"^timeinfofromseconds",TimeInfoFromSecondsCode,1,SAMELINE,"given time/date in seconds, returning a sequence of 6 matchvariables"}, 
	{"^timetoseconds",TimeToSecondsCode,VARIABLE_ARG_COUNT,SAMELINE,"given time/date in seconds, return the timeinfo string corresponding to it"}, 

	{"\r\n---- Debugging",0,0,0,""},
	{"^debug",DebugCode,VARIABLE_ARG_COUNT,SAMELINE,"only useful for debug code breakpoint"}, 
	{"^identify",IdentifyCode,0,SAMELINE,"report CS version info"}, 
	{"^log",LogCode,STREAM_ARG,0,"add to logfile"}, 

	{"\r\n---- Output Generation - not legal in post processing",0,0,0,""},
	{"^flushoutput",FlushOutputCode,0,SAMELINE,"force existing output out"}, 
	{"^insertprint",InsertPrintCode,STREAM_ARG,0,"add output before named responseIndex"},
	{"^keephistory",KeepHistoryCode,2,SAMELINE,"trim history of USER or BOT to number of entries given"}, 
	{"^print",PrintCode,STREAM_ARG,0,"isolated output message from current stream"}, 
	{"^preprint",PrePrintCode,STREAM_ARG,0,"add output before existing output"}, 
	{"^repeat",RepeatCode,0,SAMELINE,"set repeat flag so can repeat output"}, 
	{"^reviseoutput",ReviseOutputCode,2,0,"takes index and output, replacing output at that index"}, 

	{"\r\n---- Output Access",0,0,0,""},
	{"^lastsaid",LastSaidCode,0,0,"get what chatbot said just before"},
	{"^response",ResponseCode,1,0,"raw text for this response, including punctuation"},
	{"^responsequestion",ResponseQuestionCode,1,SAMELINE,"BOOLEAN - 1 if response ends in ?  0 otherwise"}, 
	{"^responseruleid",ResponseRuleIDCode,1,SAMELINE,"rule tag generating this response"},
	
	{"\r\n---- Postprocessing functions - only available in postprocessing",0,0,0,""},
	{"^postprintbefore",PostPrintBeforeCode,STREAM_ARG,0,"add to front of output stream"}, 
	{"^postprintafter",PostPrintAfterCode,STREAM_ARG,0,"add to end of output stream"}, 

	{"\r\n---- Control Flow",0,0,0,""},
	{"^argument",ArgumentCode,VARIABLE_ARG_COUNT,0,"returns the calling scope's nth argument (given n and possible fn name)"},
	{"^addcontext",AddContextCode,2,0,"set topic and label as a context"},
	{"^command",CommandCode,STREAM_ARG,0,"execute a : command"}, 
	{"^end",EndCode,1,SAMELINE,"cease current processing thru this level"}, 
	{"^eval",EvalCode,STREAM_ARG,0,"evaluate stream"}, 
	{"^fail",FailCode,1,SAMELINE,"return a return code of some kind - allowed to erase facts on sentence fail"}, 
	{"^match",MatchCode,STREAM_ARG,0,"Perform given pattern match"},
	{"^nofail",NoFailCode,STREAM_ARG,0,"execute script but ignore all failures thru some level"}, 
	{"^notnull",NotNullCode,STREAM_ARG,0,"tests that output of stream argument is not null, fails otherwise"}, 
	{"^result",ResultCode,STREAM_ARG,0,"executes the stream and returns the result code (never fails) "}, 
	{"^retry",RetryCode,VARIABLE_ARG_COUNT,SAMELINE,"reexecute a rule with a later match or retry  input"},
	{"^memorymark",MemoryMarkCode,0,0,"note memory information for later memory free"}, 
	{"^memoryfree",MemoryFreeCode,0,0,"release dict,fact,text allocated since last memorymark"},
	{"^incontext",InContextCode,1,0,"returns normally if given label or topic.label have output recently else fails"},

#ifndef DISCARDDATABASE
	{"\r\n---- Database",0,0,0,""},
	{"^dbinit",DBInitCode,STREAM_ARG,0,"access a postgres database"}, 
	{"^dbclose",DBCloseCode,0,0,"close current postgres database"}, 
	{"^dbexecute",DBExecuteCode,STREAM_ARG,0,"perform postgres transactions"}, 
	{"^PGUserFiles",PGUserFilesCode,STREAM_ARG,0,"use postgres to store users"}, 
	{"^PGUserFilesClose",PGUserFilesCloseCode,STREAM_ARG,0,"close postgres to store users"}, 
#endif

	{"\r\n---- Word Manipulation",0,0,0,""},
	{"^addproperty",AddPropertyCode,STREAM_ARG,0,"Add value to dictionary entry properies or systemFlags or facts of factset properties"}, 
	{"^burst",BurstCode,VARIABLE_ARG_COUNT,0,"break a string into component words either to facts or matchvars - if 1st arg is wordcount, returns number of words"}, 
	{"^define",DefineCode,VARIABLE_ARG_COUNT,0,"get dictionary gloss of  word"}, 
	{"^explode",ExplodeCode,1,0,"break a word into component letters"}, 
	{"^extract",ExtractCode,3,0,"pull out text from given string starting at position and ending at position"}, 
	{"^findtext",FindTextCode,VARIABLE_ARG_COUNT,0,"locate start position in target of given string starting at offset"}, 
	{"^flags",FlagsCode,1,0,"get flag values of word"}, 
	{"^hasanyproperty",HasAnyPropertyCode,VARIABLE_ARG_COUNT,0,"argument 1 has any of property or systemflags of argument2 .. argumentn"}, 
    {"^hasallproperty",HasAllPropertyCode,VARIABLE_ARG_COUNT,0,"argument 1 has all of the properties or systemflags of argument2 .. argumentn"}, 
	{"^uppercase",UppercaseCode,1,0,"boolean return 1 if word was entered uppercase, 0 if not"}, 
	{"^properties",PropertiesCode,1,0,"get property values of word"}, 
	{"^intersectwords",IntersectWordsCode,VARIABLE_ARG_COUNT,0,"see if words in arg 1 are in arg2"},
	{"^join",JoinCode,STREAM_ARG,OWNTRACE,"merge words into one"}, 
	{"^pos",English_POSCode,VARIABLE_ARG_COUNT,0,"compute some part of speech value"},
	{"^removeinternalflag",RemoveInternalFlagCode,2,0,"Remove internal flag from word- currently only HAS_SUBSTITUTE"}, 
	{"^removeproperty",RemovePropertyCode,STREAM_ARG,0,"remove value to dictionary entry properies or systemFlags or facts of factset properties"},
	{"^rhyme",RhymeCode,1,0,"find a rhyming word"}, 
	{"^substitute",SubstituteCode,VARIABLE_ARG_COUNT,0,"alter a string by substitution"}, 
	{"^spell",SpellCode,1,0,"find words matching pattern and store as facts"}, 
	{"^sexed",SexedCode,4,0,"pick a word based on sex of given word"}, 
	{"^tally",TallyCode,VARIABLE_ARG_COUNT,0,"get or set a word value"},
	{"^walkdictionary",WalkDictionaryCode,1,0,"call a function on every word in the dictionary"},
#ifndef DISCARDCOUNTER
	{"^wordcount",WordCountCode,VARIABLE_ARG_COUNT,0,"get or set a word count value"},
#endif
	
	{"\r\n---- MultiPurpose Functions",0,0,0,""},
	{"^disable",DisableCode,VARIABLE_ARG_COUNT,SAMELINE,"stop a RULE or TOPIC or INPUTREJOINDER or OUTPUTREJOINDER or SAVE"}, 
	{"^enable",EnableCode,VARIABLE_ARG_COUNT,SAMELINE,"allow a rule or topic"}, 
	{"^length",LengthCode,1,SAMELINE,"counts characters in a word or members of a fact set or top level concept members"}, 
	{"^next",NextCode,STREAM_ARG,0,"FACT- walk a factset without erasing it  GAMBIT,RESPONDER,RULE,REJOINDER with tag or label for next one  INPUT to go to next sentence"}, 
	{"^pick",FLRCodeR,STREAM_ARG,0,"randomly select and remove an element from a factset or randomly select from a concept"}, 
	{"^reset",ResetCode,VARIABLE_ARG_COUNT,0,"reset a topic or all topics or user or pending output back to initial state "}, 

	{"\r\n---- Functions on facts",0,0,0,""},
	{"^conceptlist",ConceptListCode,STREAM_ARG,0,"create facts of the concepts or topics or both triggers by word at position or overall"}, 
	{"^createattribute",CreateAttributeCode,STREAM_ARG,OWNTRACE,"create a triple where the 3rd field is exclusive"}, 
	{"^createfact",CreateFactCode,STREAM_ARG,OWNTRACE,"create a triple"}, 
	{"^delete",DeleteCode,1,0,"delete all facts in factset or delete named fact"}, 
	{"^field",FieldCode,2,0,"get a field of a fact"}, 
	{"^find",FindCode,2,0,"Given set or factset, find ordinal position of item within it"},
	{"^findfact",FindFactCode,3,0,"given simple non-facts subject verb object, see if fact exists of it"},
	{"^findmarkedfact",FindMarkedFactCode,3,0,"given a subject,a verb, and a mark, return a marked fact that can be found propogating from subject using verb  or null"},
	{"^first",FLRCodeF,STREAM_ARG,0,"get first element of a factset and remove it"},
	{"^flushfacts",FlushFactsCode,1,0,"erase all facts created after here"}, 
	{"^intersectfacts",IntersectFactsCode,STREAM_ARG,0,"find facts common to two factsets, based on fields"},
	{"^iterator",IteratorCode,3,0,"walk facts of some thing"},
	{"^makereal",MakeRealCode,0,0,"make all transient facts non-transient"},
	{"^nth",FLRCodeSpecific,2,0,"from factset get nth element (kept) or from set get nth element"},
	{"^revisefact",ReviseFactCode,4,OWNTRACE,"revise a triple"}, 
	{"^uniquefact",UniqueFactsCode,STREAM_ARG,0,"find facts in first set not found in second"},
	{"^last",FLRCodeL,STREAM_ARG,0,"get last element of a factset and remove it"},
	{"^query",QueryCode,STREAM_ARG,0,"hunt for fact in fact database"},
	{"^sort",SortCode,STREAM_ARG,0,"sort facts on named set-field (presumed number) low to high"},
	{"^unduplicate",UnduplicateCode,1,0,"remove duplicate facts"},
	{"^unpackfactref",UnpackFactRefCode,1,0,"copy out fields which are facts"}, 

	{"\r\n---- External Access",0,0,0,""},
	{"^export",ExportFactCode,VARIABLE_ARG_COUNT,SAMELINE,"write fact set to a file"},
	{"^import",ImportFactCode,4,SAMELINE,"read fact set from a file"}, 
	{"^system",SystemCode,STREAM_ARG,SAMELINE,"send command to the operating system"},
	{"^popen",PopenCode,2,SAMELINE,"send command to the operating system and read reply strings"},
	{"^tcpopen",TCPOpenCode,4,SAMELINE,"send command to website and read reply strings"},

	{0,0,0,0,""}	
};
