from lexer import Id, Array, Integer
import os

class Generator:
    def __init__(self):
        pass

    def do(self, suite, outFile):
        for case in suite:
            outFile.write(case.Body() + os.linesep)
