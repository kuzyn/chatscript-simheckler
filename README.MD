# SimHeckler
### Think like a heckler... BE THE HECKLER!

_v0.0.1 / Mai 2015_  
CS 5.31

### Installation
* download & install the latest [Chatscript](http://sourceforge.net/projects/chatscript/files/latest/download?source=files) version
* drop this repo into the ChatScript directory
* on Linux, ```cd``` to directory and do ```./LinuxChatScript* local```
* do ``` :build Heckler ```
* heckle!!!

### Intentions

_The heckler’s game AKA "An evening as James Carlton"_

>"But heckling is something else. At its best, it is almost a conspiracy between the heckler and the heckled,
born out of mutual antagonism but mitigated by combative wit; a gamble, too, since neither player can be
sure that he ­ it is usually a testosterone­charged he ­ will come off best."
>
>_The Guardian, A brief history of heckling, Michael White 2006_

You are an audience member at a comedy show. The comedian is telling jokes. Your are
heckling him. That is, you interrupt his monologue with witty counters, insults and interferences.
Your goal is to steal the show, his goal is to nail you with hard to follow retorts or retort to your
retorts.

The longer the volley, the bigger the stakes. If you cannot "connect", that is connect your retorts
with what the comedian is saying, he wins. Every (chosen) intervention is a short bout where
both participant try to outwit or trap the other.

#### General Design Goals ####
1. Volley scoring system
1. Natural recoveries and follow­up
1. Non­linear, block­based stand­up routine
1. Minimal visual representations
1. Extensive but generic repertoire

#### Game Design ####
* Points are gained and lost during exchanges
* The player can "stay pat" and not intervene; the monologue continue nonetheless
* The player tries to accumulate points by connecting with the comedian’s jokes
* The player tries to preserve points by avoiding hard or slippery counter retorts
* Harder to connect jokes yield more points
* The longer the rally, the bigger the stakes (points add up during a round/joke)
* A good analogy would be the game of battle (playing cards): drawing two identical cards
let the duel continues with a "winner take all" condition
* The comedian (Chatbot) have a limit within a volley where he has to forfeit, as the dealer hitting 17 at Blackjack.
 
**Exemple:**
Let’s assume that one joke is one "round" (r) and that each volley is worth one point.  
  r1#0 ~Comedian: So I was having dinner with my wife, right…  
  r1#1 ~Player: Your wife’s a whore!  
  r1#1 ~Comedian: Don’t you think it’s a harsh thing to say about your mom?  
  r1#!= ~Player: Fuck you. _[Does not connect or relate]_  
  r2#0 ~Comedian: Whatever, buddy. So I was having dinner with my wife, right…  
  **[Player’s score ­= 1 point] [Comedian’s annoyance += 1 point]** 

Three branches of end game scenarios:  

1. **Quick streak**
   1. The player steals the show with an uninterrupted and successful streak, the comedian leaves, *the player win*
   2. The player gets chewed up by the comedian during an uninterrupted streak on his part, *the player lose*
2. **Routine end**
   1. The comedy routine is over, the player have a bigger score than the comedian, *the player win*
   2. The comedy routine is over, the comedian has a bigger score than the player, *the player lose*
3. **Does not connect**
   1. The player does not rally but only interrupts or insults the comedian, the comedian is annoyed and leaves, *the player lose*

### Preliminary References

[A brief history of heckling](http://www.theguardian.com/politics/2006/apr/28/past.labour)  
[YOU'RE UGLY, YOUR DICK IS SMALL AND EVERYBODY FUCKS YOUR MOTHER:
THE STAND UP COMEDIAN'S RESPONSE TO THE HECKLER](http://www.juggling.org/~conway/juggler/MAL.TXT)  
[Maledicta: The International Journal of Verbal Aggression](http://aman.members.sonic.net/)  
[The Art of Stand Up](https://www.youtube.com/watch?v=AguHpfT2Tqc)  
[Statler and Waldorf](http://en.wikipedia.org/wiki/Statler_%26_Waldorf)  
