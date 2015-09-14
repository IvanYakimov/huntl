# ifndef __PARSER_HPP_
# define __PARSER_HPP_

#include "llvm/IR/Verifier.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"

# include "ast.hpp"
# include "lexer.hpp"
# include <map>
# include <cstdio>

void InitParser ();

void PrimeFirstToken ();
void MainLoop ();

static void HandleDefinition ();
static void HandleExtern ();
static void HandleTopLevelExpr ();

static int getNextToken ();
static int GetTokPrecedence ();
static ExprAST *ParseNumberExpr ();
static ExprAST *ParseIdentifierExpr ();
static ExprAST *ParseParenExpr ();
static ExprAST *ParsePrimary ();
static ExprAST *ParseExpression ();
static ExprAST *ParseBinOpRHS (int ExprPrec, ExprAST *LHS);

static PrototypeAST *ParsePrototype ();
static PrototypeAST *ParseExtern ();
static FunctionAST *ParseDefinition ();
static FunctionAST *ParseTopLevelExpr ();

# endif /* __PARSER_HPP__ */
