//http://2015.hackitoergosum.org/slides/HES2015-10-29%20Cracking%20Sendmail%20crackaddr.pdf
#define BUFFERSIZE 200
#define TRUE 1
#define FALSE 0 
int
copy_it (char *input, unsigned int length)
{
	char c, localbuf[BUFFERSIZE];
	unsigned int upperlimit = BUFFERSIZE - 10;
	unsigned int quotation = FALSE;
	unsigned int roundquote = FALSE;
	unsigned int inputIndex = 0;
	unsigned int outputIndex = 0;
	while (inputIndex < length)
	  {
		  c = input[inputIndex++];
		  if ((c == '<') && (!quotation))
		    {
			    quotation = TRUE;
			    upperlimit --;
		    }
		  if ((c == '>') && (quotation))
		    {
			    quotation = FALSE;
			    upperlimit++;
		    }
		  if ((c == '(') && (!quotation) && !roundquote)
		    {
			    roundquote = TRUE;
			    upperlimit--;	// decrementation was missing in bug
		    }
		  if ((c == ')') && (!quotation) && roundquote)
		    {
			    roundquote = FALSE;
			    upperlimit++;
		    }
// If there is sufficient space in the buffer , write the character .
		  if (outputIndex < upperlimit)
		    {
			    localbuf[outputIndex] = c;
			    //prove that outputIndex < BUFFERSIZE holds
				    outputIndex++;
		    }
	  }
	if (roundquote)
	  {
		  //prove that invariant outputIndex < BUFFERSIZE holds
			  localbuf[outputIndex] = ')';
		  outputIndex++;
	  }
	if (quotation)
	  {
		  //prove that invariant outputIndex < BUFFERSIZE holds
			  localbuf[outputIndex] = '>';
		  outputIndex++;
	  }
}


int
main(int argc, char argv[]){
char buffer[200];
read(0,buffer,200);
copy_it(buffer, 200);
return 0;
}
