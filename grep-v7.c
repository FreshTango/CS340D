/* Lab 3
   Khiem Tang 
*/

/* UNIX V7 source code: see /COPYRIGHT or www.tuhs.org for details. */

/*
 * grep -- print lines matching (or not matching) a pattern
 *
 *	status returns:
 *		0 - ok, and some matches
 *		1 - ok, but no matches
 *		2 - some error
 */

/* Changes for ANSI C Conformance:

- Adjusted layout of arguments on subroutine headers.
- Added stdlib.h library
- Added implicit declarations of subroutines above main function.
- Added specificity to 'register' type variables for compatibility.
- Added return values to certain cases.
- Adjusted printf formatting for compatibility.
- Changed macro BSIZE to DEV_BSIZE.

*/

#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <sys/param.h>

#define	CBRA	1 // Denotes the beginning of a group in the expression. (e.g.: "\(abc\)")
#define	CCHR	2 // Designated for a character.
#define	CDOT	4 // Designated for a period.
#define	CCL	    6 // Denotes ranges. (e.g.: [A-Z])
#define	NCCL	8 // This constant does not seem to be used.
#define	CDOL	10 // Denotes the matching of an expression at the end of a line. (e.g.: "abc$")
#define	CEOF	11 // Denotes the end of the pattern expression.
#define	CKET	12 // Denotes the closure or end of a group.
#define	CBACK	18 // Denotes a backreference.

#define	STAR	01 // Denotes the asterisk special character (e.g.: "abc*").

#define	LBSIZE	512 // Defines the maximum size of the buffer for the file line.
#define	ESIZE	256 // Defines the maximum size of the buffer for the pattern.
#define	NBRA	9 // Denotes the maximum amount of groups possible.

char	expbuf[ESIZE]; // Defines the compiled or processed version of the pattern.
long	lnum; // Defines the current line number of the file. 
char	linebuf[LBSIZE+1]; // Defines the buffer for the line of the file.
char	ybuf[ESIZE]; // Defines the "case-insensitive" buffer.
int	bflag; // Status of b flag: Print the offset of the line containing the match.
int	lflag; // Status of l flag: When match is found, print the name of the input file.
int	nflag; // Status of n flag: Prefix each line of output with corresponding line number.
int	cflag; // Status of c flag: Prints the count of matching lines.
int	vflag; // Status of v flag: Selects non-matching lines.
int	nfile; // Defines the number of files. 
int	hflag	= 1; // Status of h flag: Suppress the prefixing of file names on output. (e.g. file.txt: <data>)
int	sflag; // Status of s flag: Suppress error messages about nonexistent/unreadable files.
int	yflag; // Status of y flag: "Case-insensitive" (e.g.: a => [aA]; A => A)
int	circf; // Denotes whether there is a caret (^) at the beginning of the pattern.
long	tln; // Denotes the number of matching lines given the inputted pattern, with the c flag.
int	nsucc; // Determines whether or not a match is found. Set to 0 if match, 1 if no match.
char	*braslist[NBRA]; // Denotes the pointers for the beginning of groups. Used for backreferences.
char	*braelist[NBRA]; // Denotes the pointers for the end of groups. Used for backreferences.
char	bittab[] = { // A bit table defined to mask the last three bits of the expression for use in comparison.
	1,
	2,
	4,
	8,
	16,
	32,
	64,
	128
};

// Implicit declaration calls of subroutines.
int compile(char *astr);
int errexit(char *s, char *f);
int execute(char *file);
int advance(register char *lp, register char *ep);
int succeed(char *f);
int ecmp(char *a, char *b, int count);
int errexit(char *s, char *f);

/* Main: Reads the input given from the grep call and parses it.
	Iterates through argc & argv, marks which flags are set. */
int main (int argc, char **argv)
{
	// Reads in the arguments from the command line and determines set flags.
	while (--argc > 0 && (++argv)[0][0]=='-')
		switch (argv[0][1]) {

		case 'y':
			yflag++;
			continue;

		case 'h':
			hflag = 0;
			continue;

		case 's':
			sflag++;
			continue;

		case 'v':
			vflag++;
			continue;

		case 'b':
			bflag++;
			continue;

		case 'l':
			lflag++;
			continue;

		case 'c':
			cflag++;
			continue;

		case 'n':
			nflag++;
			continue;

		case 'e':
			--argc;
			++argv;
			goto out;

		default:
			errexit("grep: unknown flag\n", (char *)NULL);
			continue;
		}
out:
	if (argc<=0)
		exit(2);
	if (yflag) {
		register char *p, *s;
		for (s = ybuf, p = *argv; *p; ) {
			if (*p == '\\') {
				*s++ = *p++;
				if (*p)
					*s++ = *p++;
			} else if (*p == '[') {
				while (*p != '\0' && *p != ']')
					*s++ = *p++;
			} else if (islower(*p)) {
				*s++ = '[';
				*s++ = toupper(*p);
				*s++ = *p++;
				*s++ = ']';
			} else
				*s++ = *p++;
			if (s >= ybuf+ESIZE-5)
				errexit("grep: argument too long\n", (char *)NULL);
		}
		*s = '\0';
		*argv = ybuf;
	}
	compile(*argv);
	nfile = --argc;
	if (argc<=0) {
		if (lflag)
			exit(1);
		execute((char *)NULL);
	} else while (--argc >= 0) {
		argv++;
		execute(*argv);
	}
	exit(nsucc == 0);
}

/* Compile: Checks the syntax of the given pattern, throwing
an errexit call if the syntax is incorrect. Once the syntax is deemed
valid, the expression is parsed and converted into a readable format
for grep, particularly useful for the execute function.
[Input]: Pattern expression (e.g. "dddd")
[Output]: 
 2  64  2  64  2  64  2  64  b  0 
 0  0  0  0  0  ...
[Explanation]:
The first 2 in the table represents a character type
(denoted by the CCHR macro), followed by 64 in hex (d in ascii). */
int compile(char *astr)
{
	register int c;
	register char *ep, *sp;
	char *cstart;
	char *lastep;
	int cclcnt;
	char bracket[NBRA], *bracketp;
	int closed;
	char numbra;
	char neg;

	ep = expbuf;
	sp = astr;
	lastep = 0;
	bracketp = bracket;
	closed = numbra = 0;
	if (*sp == '^') {
		circf++;
		sp++;
	}
	for (;;) {
		if (ep >= &expbuf[ESIZE])
			goto cerror;
		if ((c = *sp++) != '*')
			lastep = ep;
		switch (c) {

		case '\0':
			*ep++ = CEOF;
			return 0;

		case '.':
			*ep++ = CDOT;
			continue;

		case '*':
			if (lastep==0 || *lastep==CBRA || *lastep==CKET)
				goto defchar;
			*lastep |= STAR;
			continue;

		case '$':
			if (*sp != '\0')
				goto defchar;
			*ep++ = CDOL;
			continue;

		case '[':
			if(&ep[17] >= &expbuf[ESIZE])
				goto cerror;
			*ep++ = CCL;
			neg = 0;
			if((c = *sp++) == '^') {
				neg = 1;
				c = *sp++;
			}
			cstart = sp;
			do {
				if (c=='\0')
					goto cerror;
				if (c=='-' && sp>cstart && *sp!=']') {
					for (c = sp[-2]; c<*sp; c++)
						ep[c>>3] |= bittab[c&07];
					sp++;
				}
				ep[c>>3] |= bittab[c&07];
			} while((c = *sp++) != ']');
			if(neg) {
				for(cclcnt = 0; cclcnt < 16; cclcnt++)
					ep[cclcnt] ^= -1;
				ep[0] &= 0376;
			}

			ep += 16;

			continue;

		case '\\':
			if((c = *sp++) == '(') {
				if(numbra >= NBRA) {
					goto cerror;
				}
				*bracketp++ = numbra;
				*ep++ = CBRA;
				*ep++ = numbra++;
				continue;
			}
			if(c == ')') {
				if(bracketp <= bracket) {
					goto cerror;
				}
				*ep++ = CKET;
				*ep++ = *--bracketp;
				closed++;
				continue;
			}

			if(c >= '1' && c <= '9') {
				if((c -= '1') >= closed)
					goto cerror;
				*ep++ = CBACK;
				*ep++ = c;
				continue;
			}

		defchar:
		default:
			*ep++ = CCHR;
			*ep++ = c;
		}
	}
    cerror:
	errexit("grep: RE error\n", (char *)NULL);
}

/* Execute: Takes the converted expression from compile and interprets
it to find applicable matches in the inputted file. The function will open
a file and begin to iterate through it line by line and compare it to the 
converted expression (linebuf & expbuf) attempting to detect matches. 
[Input]: Given file
[Output]: Match is printed */
int execute(char *file)
{
	register char *p1, *p2;
	register char c;

	if (file) {
		if (freopen(file, "r", stdin) == NULL)
			errexit("grep: can't open %s\n", file);
	}
	lnum = 0;
	tln = 0;
	for (;;) {
		lnum++;
		p1 = linebuf;
		while ((c = getchar()) != '\n') {
			if (c == EOF) {
				if (cflag) {
					if (nfile>1)
						printf("%s:", file);
					printf("%ld\n", tln);
				}
				return 0;
			}
			*p1++ = c;
			if (p1 >= &linebuf[LBSIZE-1])
				break;
		}
		*p1++ = '\0';
		p1 = linebuf;
		p2 = expbuf;
		if (circf) {
			if (advance(p1, p2))
				goto found;
			goto nfound;
		}
		/* fast check for first character */
		if (*p2==CCHR) {
			c = p2[1];
			do {
				if (*p1!=c)
					continue;
				if (advance(p1, p2))
					goto found;
			} while (*p1++);
			goto nfound;
		}
		/* regular algorithm */
		do {
			if (advance(p1, p2))
				goto found;
		} while (*p1++);
	nfound:
		if (vflag)
			succeed(file);
		continue;
	found:
		if (vflag==0)
			succeed(file);
	}
}

/* Advance: Takes in the line and expression buffer and compares the two,
at last outputting whether there is a match or not. Returns 1 if match
or 0 if there is not a match. This function is called recursively whenever
there is a character followed by an asterisk (CCHR | STAR).
[Input]: Line and expression buffers (linebuf & expbuf)
[Output]: Returns 1 if match, 0 if not a match. */
int advance(register char *lp, register char *ep)
{
	register char *curlp;
	char c;
	char *bbeg;
	int ct;

	for (;;) switch (*ep++) {

	case CCHR:
		if (*ep++ == *lp++)
			continue;
		return(0);

	case CDOT:
		if (*lp++)
			continue;
		return(0);

	case CDOL:
		if (*lp==0)
			continue;
		return(0);

	case CEOF:
		return(1);

	case CCL:
		c = *lp++ & 0177;
		if(ep[c>>3] & bittab[c & 07]) {
			ep += 16;
			continue;
		}
		return(0);
	case CBRA:
		braslist[*ep++] = lp;
		continue;

	case CKET:
		braelist[*ep++] = lp;
		continue;

	case CBACK:
		bbeg = braslist[*ep];
		if (braelist[*ep]==0)
			return(0);
		ct = braelist[*ep++] - bbeg;

		if(ecmp(bbeg, lp, ct)) {
			lp += ct;
			continue;
		}
		return(0);

	case CBACK|STAR:
		bbeg = braslist[*ep];
		if (braelist[*ep]==0)
			return(0);
		ct = braelist[*ep++] - bbeg;
		curlp = lp;
		if (ct == 0)
			continue;
		while(ecmp(bbeg, lp, ct))
			lp += ct;
		while(lp >= curlp) {
			if(advance(lp, ep))	return(1);
			lp -= ct;
		}
		return(0);


	case CDOT|STAR:
		curlp = lp;
		while (*lp++);
		goto star;

	case CCHR|STAR:
		curlp = lp;
		while (*lp++ == *ep);
		ep++;
		goto star;

	case CCL|STAR:
		curlp = lp;
		do {
			c = *lp++ & 0177;
		} while(ep[c>>3] & bittab[c & 07]);
		ep += 16;
		goto star;

	star:
		if(--lp == curlp) {
			continue;
		}

		if(*ep == CCHR) {
			c = ep[1];
			do {
				if(*lp != c)
					continue;
				if(advance(lp, ep))
					return(1);
			} while(lp-- > curlp);
			return(0);
		}

		do {
			if (advance(lp, ep))
				return(1);
		} while (lp-- > curlp);
		return(0);

	default:
		errexit("grep RE botch\n", (char *)NULL);
	}
}

/* Succeed: Takes in a file and prints out the matches of the given line.
[Input]: Given file
[Output]: Returns matches of the given line based on the expression. If the c flag
is set, the succeed function simply increments the long tln (count for matches) and
returns. Ultimately, different flags set alters the routine's final output. */
int succeed(char *f)
{
	long ftell();
	nsucc = 1;
	if (sflag)
		return 0;
	if (cflag) {
		tln++;
		return 0;
	}
	if (lflag) {
		printf("%s\n", f);
		fseek(stdin, 0l, 2);
		return 0;
	}
	if (nfile > 1 && hflag)
		printf("%s:", f);
	if (bflag)
		printf("%ld:", (ftell(stdin)-1)/DEV_BSIZE);
	if (nflag)
		printf("%ld:", lnum);
	printf("%s\n", linebuf);
}

/* Ecmp: Takes in two pointers to a string and a count. If the first number of characters,
defined by count, are equal, then the function returns 1. Else, the function returns 0.
The function itself is used only within backreferencing situations, and called during the execution
of the advance subroutine (which determines if there is a match).
[Input]: Two poiners to groups and a count integer.
[Output]: Return 0 or 1. */
int ecmp(char *a, char *b, int count)
{
	register int cc = count;
	while(cc--)
		if(*a++ != *b++)	return(0);
	return(1);
}

/* Errexit: General error function, which prints out an error message and exits the program.
[Input]: Error string and corresponding file.
[Output]: Error message and exit system call. */
int errexit(char *s, char *f)
{
	fprintf(stderr, s, f);
	exit(2);
}
