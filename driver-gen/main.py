#!/usr/bin/python
import sys, getopt, errno

from iosupport import openFile
from parser import Parser
from generator import Generator

def main(argv):
    opened = []
    inFile = sys.stdin
    outFile = sys.stdout
    try:
        opts, args = getopt.getopt(argv,"hi:o:", ["help","ifile=","ofile="])
    except getopt.GetoptError:
        print "Bad args. Wait for: --ifile=<name> --ofile=<name>"
        sys.exit(0)
    for opt, arg in opts:
        if opt == '-h':
            print "TODO"
            sys.exit(0)
        elif opt in ("-i", "--ifile"):
            inFile = openFile(arg, "r")
            opened.append(inFile)
        elif opt in ("-o", "--ofile"):
            outFile = openFile(arg, "w")
            opened.append(outFile)
    if inFile == sys.stdin:
        print "please, enter a string"
    parser = Parser()
    gen = Generator()
    suite = parser.do(inFile)
    print "//parsed"
    gen.do(suite, outFile)
    print "//generated"
    for f in opened:
        assert (f)
        f.close()

if __name__ == "__main__":
    main(sys.argv[1:])

# input strings line by line from stdin
