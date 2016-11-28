from lexer import Id, Array, Integer
import os

class Generator:
    def __init__(self):
        pass

    def do(self, suite, outFile):
        counter = 0
        for case in suite:
            print "void runner" + str(counter) + "()"
            outFile.write(case.Body() + os.linesep)
            counter+=1
        print "int main(){"
        for i in range(0,counter):
           print "\trunner" + str(i) + "();"
        print "}"
