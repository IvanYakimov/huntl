from testsuite import TestCase
from lexer import Lexer, Id, Arrow, Array, Integer

class Parser:
    def __init__(self):
        self.lexer = Lexer()

    def parseId(self, items):
        it = items[0]
        tok = self.lexer.match(it)
        assert (isinstance(tok, Id))
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
        tok = self.lexer.match(items[0])
        assert(isinstance(tok, Arrow))
        return tok, items[1:]

    def parseRes(self, items):
        tok = self.lexer.match(items[0])
        assert(isinstance(tok, Array) or isinstance(tok, Integer))
        items = items[1:]
        assert (items == [])
        return tok, items
    
    def do(self, inFile):
        suite = []
        for line in inFile:
            items = line.split()
            fname, items = self.parseId(items)
            args, items = self.parseArgs(items)
            arrow, items = self.parseArrow(items)
            res, items = self.parseRes(items)
            case = TestCase(fname, args, res)
            print "//", str(case)
            suite.append(case)
        return suite
                        
