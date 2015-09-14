# ifndef __LEXER_HPP__
# define __LEXER_HPP__

# include <string>
# include <cstdio>
# include <cstdlib>

/// The lexer returns tokens [0-255] if it is an unknown character,
/// otherwise one of these for known things.
enum Tokens
  {
    tok_eof = -1,
  
    // commands
    tok_def = -2, tok_extern = -3,

    // primary
    tok_identifier = -4, tok_number = -5
  };



// static
int gettok ();
std::string getIdentifierStr ();
int getNumVal ();

# endif /* __LEXER_HPP__ */
