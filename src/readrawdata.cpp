// raw data parser for dictionary.... (not needed in a product)

#include "common.h"

#ifdef DISCARDDICTIONARYBUILD
void LoadRawDictionary(int mini)
{    
	printf("Raw dictionary code not installed\r\n");
}

void BuildShortDictionaryBase()
{
}

#else
#include "../extraSrc/readrawdata.cpp"
#endif
