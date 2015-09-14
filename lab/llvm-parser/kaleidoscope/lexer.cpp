# include "lexer.hpp"

static std::string IdentifierStr; // Filled in if tok_identifier
std::string getIdentifierStr () { return IdentifierStr; }
static double NumVal; // Filled in if tok_number
int getNumVal () { return NumVal; }

/// gettok - Return the next token from standard input.
//static
int gettok ()
{
  static int LastChar = ' ';

  // Skip any whitespace.
  while (isspace (LastChar))
    LastChar = getchar ();

  // Identifiers
  if (isalpha (LastChar))
    {
      IdentifierStr = LastChar;
      while (isalnum ((LastChar = getchar ())))
	IdentifierStr += LastChar;

      if (IdentifierStr == "def") return tok_def;
      if (IdentifierStr == "extern") return tok_extern;
      return tok_identifier;
    }

  // Numeric Values [0-9.]+
  if (isdigit (LastChar) || LastChar == '.')
    {
      std::string NumStr;
      do
	{
	  NumStr += LastChar;
	  LastChar = getchar ();
	} while (isdigit (LastChar) || LastChar == '.');
      
	NumVal = strtod (NumStr.c_str (), 0);
      return tok_number;
    }

  // Comment
  if (LastChar == '#')
    {
      // Comment until end of line
      do LastChar = getchar ();
      while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');

      if (LastChar != EOF)
	return gettok ();
    }

  // Check for end of file. Don't eat the EOF.
  if (LastChar == EOF)
    return tok_eof;

  // Otherwise, just return the character as its ascii value.
  int ThisChar = LastChar;
  LastChar = getchar ();
  return ThisChar;
}
