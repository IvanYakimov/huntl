from lexer import Lexer, Id, Arrow, Array, Integer
import os

class TestCase:
    def __init__(self, fname, args, res):
        self.fname = fname
        self.args = args
        self.res = res
        
    def __str__(self):
        string = str(self.fname) + " "
        for a in self.args:
            string += str(a) + " "
        string +=  ":=> " + str(self.res)
        return string

    def Body(self):
        body = "{" + os.linesep
        idx = 0
        for a in self.args:
            idx += 1
            body += "\t" + a.Initializer("arg" + str(idx))
        body += "\t" + self.res.Declaration("res")
        body += "\tres = " + str(self.fname) + "("
        idx = 0
        for a in self.args:
            idx += 1
            body += "arg" + str(idx) + ", "
        body = body[:-2]
        body += ");" + os.linesep
        body += "}"
        return body
            
    
