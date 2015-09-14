# include "parser.hpp"

using namespace llvm;

/// CurTok/getNextToken - Provide a simple token buffer. CurTok is the current
/// token the parser is looking at. getNextToken reads another token from the
/// lexer and updates CurTok with its results.
static int CurTok;
static int getNextToken ()
{
  return CurTok = gettok ();
}

/// BinopPrecedence - This holds the precedence for each binary operator that is defined.
static std::map <char, int> BinopPrecedence;

/// GetTokPrecedence - Get the precedence of the pendging binary operator token.
static int GetTokPrecedence ()
{
  if (! isascii (CurTok))
    return -1;
  
  // Make shure it's a declared binop
  int TokPrec = BinopPrecedence [CurTok];
  if (TokPrec <= 0) return -1;
  return TokPrec;
}

/// Error* - These are little helper functions for error handling.
ExprAST *Error (const char *Str) {
  fprintf (stderr, "Error: %s\n", Str); return 0; }
PrototypeAST *ErrorP (const char *Str) { Error (Str); return 0; }
FunctionAST *ErrorF (const char *Str) { Error (Str); return 0; }

/// Parser itself.

/// primary
///   ::= identifierexpr
///   ::= numberexpr
///   ::= parenexpr
static ExprAST *ParsePrimary ()
{
  switch (CurTok)
    {
    default: return Error ("unknown token when expecting an expression");
    case tok_identifier: return ParseIdentifierExpr ();
    case tok_number: return ParseNumberExpr ();
    case '(': return ParseParenExpr ();
    }
}

/// numberexpr ::= number
static ExprAST *ParseNumberExpr ()
{
  ExprAST *Result = new NumberExprAST (getNumVal ());
  getNextToken (); // consume the number
  return Result;
}

/// parenexpr ::= '(' expression ')'
static ExprAST *ParseParenExpr ()
{
  getNextToken (); // eat (.
  ExprAST *V = ParseExpression ();
  if (!V) return 0;

  if (CurTok != ')')
    return Error ("expected ')'");
  getNextToken (); // eat ).
  return V;
}

/// identifierexpr
///   ::= identifier
///   ::= identifier '(' expression * ')'
static ExprAST *ParseIdentifierExpr ()
{
  std::string IdName = getIdentifierStr ();

  getNextToken (); // eat identifier.

  if (CurTok != '(')
    return new VariableExprAST (IdName);

  // Call.
  getNextToken (); // eat (.
  std::vector <ExprAST*> Args;
  if (CurTok != ')')
    {
      while (true)
	{
	  ExprAST *Arg = ParseExpression ();
	  if (!Arg) return 0;
	  Args.push_back (Arg);

	  if (CurTok == ')') break;

	  if (CurTok != ',')
	    return Error ("Expected ')' or ',' in argument list");
	  getNextToken ();
	}
    }

  // Eat the ')'.
  getNextToken ();

  return new CallExprAST (IdName, Args);
}

/// expression
///   ::= primary binoprhs
///
static ExprAST *ParseExpression ()
{
  ExprAST *LHS = ParsePrimary ();
  if (!LHS) return 0;

  return ParseBinOpRHS (0, LHS);
}

/// binophs
///   ::= ('+' primary)*
static ExprAST *ParseBinOpRHS (int ExprPrec, ExprAST *LHS)
{
  // If this a binop, find its precedence.
  while (true)
    {
      int TokPrec = GetTokPrecedence ();

      // If this is a binop that binds at least as tightly as
      // the current binop, consume it, otherwise we are done.
      if (TokPrec < ExprPrec)
	return LHS;

      // Okay, we know this is a binop.
      int BinOp = CurTok;
      getNextToken (); // eat binop

      // Parse the primary expression after the binary operator.
      ExprAST *RHS = ParsePrimary ();
      if (!RHS) return 0;

      // If BinOp binds less tightly with RHS than the operator
      // after RHS, let the pending operator take RHS as its LHS.
      int NextPrec = GetTokPrecedence ();
      if (TokPrec < NextPrec)
	{
	  RHS = ParseBinOpRHS (TokPrec + 1, RHS);
	  if (RHS == 0) return 0;
	}

      // Merhe LHS/RHS
      LHS = new BinaryExprAST (BinOp, LHS, RHS);
    }  // loop around to the top of while loop.
}

/// prototype
///   ::= id '(' id* ')'
static PrototypeAST *ParsePrototype ()
{
  if (CurTok != tok_identifier)
    return ErrorP ("Expected function name in prototype");

  std::string FnName = getIdentifierStr ();
  getNextToken ();

  if (CurTok != '(')
    return ErrorP ("Expected '(' in prototype");

  // Read the list of argument names.
  std::vector <std::string> ArgNames;
  while (getNextToken () == tok_identifier)
    ArgNames.push_back (getIdentifierStr ());

  if (CurTok != ')')
    return ErrorP ("Expected ')' in prototype");

  // success.
  getNextToken (); // eat ')'.

  return new PrototypeAST (FnName, ArgNames);
}

/// definition ::= 'def' prototype expression
static FunctionAST *ParseDefinition ()
{
  getNextToken (); // eat def.
  PrototypeAST *Proto = ParsePrototype ();
  if (Proto == 0) return 0;

  if (ExprAST *E = ParseExpression ())
    return new FunctionAST (Proto, E);
  return 0;
}

/// external ::= 'extern' prototype
static PrototypeAST *ParseExtern ()
{
  getNextToken (); // eat extern.
  return ParsePrototype ();
}

/// toplevelexpr ::= expression
static FunctionAST *ParseTopLevelExpr ()
{
  if (ExprAST *E = ParseExpression ())
    {
      // Make an anonymous proto.
      PrototypeAST *Proto = new PrototypeAST
	("", std::vector <std::string> ());
      return new FunctionAST (Proto, E);
    }
  return 0;
}

static void HandleDefinition ()
{
  if (FunctionAST *F = ParseDefinition ())
    {
      if (Function *LF = F->Codegen ())
	{
	  fprintf (stderr, "Read function definition:");
	  LF->dump ();
	}
    }
  else
    {
      // Skip token for error recovery.
      getNextToken ();
    }
}

static void HandleExtern ()
{
  if (PrototypeAST *P = ParseExtern ())
    {
      if (Function *F = P->Codegen ())
	{
	  fprintf (stderr, "Read extern: ");
	  F->dump ();
	}
    }
  else
    {
      // Skip token for error recovery.
      getNextToken ();
    }
}

static void HandleTopLevelExpr ()
{
  // Evaluate a top-level expression into a anonymous function.
  if (FunctionAST *F = ParseTopLevelExpr ())
    {
      if (Function *LF = F->Codegen ())
	{
	  fprintf (stderr, "Parsed a top-level expr\n");
	  LF->dump ();
	}
    }
  else
    {
      // Skip token for error recovery.
      getNextToken ();
    }
}

/// top ::= definition | external | expression | ';'
void MainLoop ()
{
  while (true)
    {
      fprintf (stderr, "> ");
      switch (CurTok)
	{
	case tok_eof: fprintf (stderr, "\n"); return;
	case ';': getNextToken (); break;
	case tok_def: HandleDefinition (); break;
	case tok_extern: HandleExtern (); break;
	default: HandleTopLevelExpr (); break;
	}
    }
}


int main ()
{
  // Install standard library operators
  // 1 is lowest precedence.
  BinopPrecedence ['<'] = 10;
  BinopPrecedence ['+'] = 20;
  BinopPrecedence ['-'] = 20;
  BinopPrecedence ['*'] = 40; // highest

  // Prime the first token.
  fprintf (stderr, "> ");
  getNextToken ();

  // Make the module, which holds all the code.
  InitModule ();

  // Run the main "interpreter loop" now.
  MainLoop ();

  // Print out all the generated code.
  Dump ();

  return 0;
}
