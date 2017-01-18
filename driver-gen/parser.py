from testsuite import TestCase
from lexer import Lexer, LexerError, Id, Arrow, Array, Integer

class ParsingError(Exception):
    def __init__(self, msg):
        self.msg = msg
    def __str__(self):
        return repr(self.msg)

class Parser:
    def __init__(self):
        self.lexer = Lexer()

    def parseId(self, items):
        tok = self.lexer.match(items[0])
        if not isinstance(tok, Id):
            raise ParsingError("Expected ID but given " + str(tok))
        return tok, items[1:]

    def parseArgs(self, items):
        result = []
        while True:
            tok = self.lexer.match(items[0])
            if isinstance(tok, Array) or isinstance(tok, Integer):
                result.append(tok)
                items = items[1:]
            else:
                break
        return result, items

    def parseArrow(self, items):
        it = items[0]
        tok = self.lexer.match(it)
        if not isinstance(tok, Arrow):
            raise ParsingError("Expected :=> but given " + str(tok))
        return tok, items[1:]

    def parseRes(self, items):
        tok = self.lexer.match(items[0])
        if not (isinstance(tok, Array) or isinstance(tok, Integer)):
            raise ParsingError(it)
        items = items[1:]
        if not items == []:
            raise ParsingError("Expected ENDL but given " + str(items))
        return tok, items
    
    def do(self, inFile):
        suite = []
        try:
            for line in inFile:
                items = line.split()
                name, items = self.parseId(items)
                args, items = self.parseArgs(items)
                arrow, items = self.parseArrow(items)
                res, items = self.parseRes(items)
                case = TestCase(name, args, res)
                print "//", str(case)
                suite.append(case)
        except ParsingError as e:
            print e.msg
            exit (0)
        except LexerError as e:
            print "Unrecognized toked: '", e.msg, "'"
            exit (0)
        except IndexError as e:
            print "Token expected"
            exit (0)
        return suite
                        
