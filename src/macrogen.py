#!/usr/bin/env python
import fileinput
import sys
#see: https://www.tutorialspoint.com/python/python_xml_processing.htm
import xml.sax
funcTag = "func"
intTy = "$INT"
funcList = []
kFunc = "func"
kName = "name"
kRet = "ret"
kHeader = "header"
kNone = ""

class FunctionHandler (xml.sax.ContentHandler):
    def __init__(self):
        self.openedTag = ""
        self.currentString = ""

    def reset(self):
        self.openedTag = ""
        self.currentString = ""

    def startElement(self, tag, atts):
        self.openedTag = tag
        if self.openedTag == funcTag:
            self.name = atts["name"]
            
    def endElement(self, tag):
        if tag == kFunc:
            func = (self.name, self.ret, self.header)
            funcList.append(func)
            self.reset()
            
    def characters(self, str):
        if self.openedTag == kRet:
            self.ret = str
        elif self.openedTag == kHeader:
            self.header = str
        self.openedTag = kNone
    
parser = xml.sax.make_parser()
parser.setFeature(xml.sax.handler.feature_namespaces,0)
handler = FunctionHandler()
parser.setContentHandler(handler)

parser.parse(sys.stdin)

for i in ["i8", "i16", "i32", "i64"]:
    for func in funcList:
        name = func[0]
        ret = func[1]
        header = func[2]
        print ret + " " + name + header.replace("$INT", i) + ";"
