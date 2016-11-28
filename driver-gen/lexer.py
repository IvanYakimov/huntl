import re
import os

class Id:
    def __init__(self, name):
        self.name = name
    def __str__(self):
        return self.name

class Array:
    def __init__(self, data):
        assert (type(data) is list and all(isinstance(n, int) for n in data))
        self.data = data
    def __str__(self):
        return '{' + str(self.data)[1:-1] + '}'
    def Initializer(self, target):
        return "int " + target + "[] = " + str(self) + ";" + os.linesep
    def Declaration(self, target):
        return "int *" + target + " = NULL;" + os.linesep

class Integer:
    def __init__(self, value):
        assert (isinstance(value,int))
        self.value = value
    def __str__(self):
        return str(self.value)
    def Initializer(self, target):
        return "int " + target + " = " + str(self) + ";" + os.linesep

class Arrow:
    def __init__(self):
        pass
    def __str__(self):
        return ":=>"
    
class Lexer:
    def __init__(self):
        pass
    
    def match(self, string):
        if re.match("\w+:$", string):
            return Id(string[:-1])
        elif re.match("^-?[0-9]+$", string):
            return Integer(int(string))
        elif re.match("^\&\{-?[0-9]+(\,-?[0-9]+)*\}$", string):
            return Array(map(int, string[2:-1].split(',')))
        elif string == ":=>":
            return Arrow()
        else:
            exit(1)
