#!/usr/bin/env python
import fileinput
import sys
import xml.sax

# see: https://interactivepython.org/runestone/static/pythonds/BasicDS/ImplementingaStackinPython.html
class Stack:
     def __init__(self): self.items = []
     def isEmpty(self): return self.items == []
     def push(self, item): self.items.append(item)
     def pop(self): self.items.pop()
     def top(self): return self.items[len(self.items)-1]
     def size(self): return len(self.items)
    
tagStack = Stack()
templateStack = Stack()
filety = 0
kDecl = 1
kDef = 2

def argsWarning():
    print "wrong number of arguments, use --decl of --def"
    sys.exit()

argnum = len(sys.argv)
if argnum  == 1: argsWarning()
elif argnum == 2:
    arg1 = sys.argv[1]
    if arg1 == "--decl": filety = kDecl
    elif arg1 == "--def": filety = kDef
    else: argsWarning()
else: argsWarning()

# parser
class TemplateHandler (xml.sax.ContentHandler):
    def __init__(self): pass
    
    def startElement(self, tag, atts):
        tagStack.push(tag)
        if tag == "func":
            self.name = atts["name"].strip()
        elif tag == "template":
            id_ = atts["id"].strip()
            exp = atts["exp"].strip().split()
            templateStack.push((id_, exp))

    def printTitle(self): print "\t//" + self.name
    def printDeclaration(self, header): print "\t" + header + ";"
    def printDefinition(self, header, body): print "\t" + header + "{\n\t\t" + body + "\n\t}\n"
    def declareOrdinary(self, header, body): self.printDeclaration(header)
    def defineOrdinary(self, header, body): self.printDefinition(header, body)
    def declareTemplated(self, header, body, id_, e): self.printDeclaration(header.replace(id_, e))
    def defineTemplated(self, header, body, id_, e): self.printDefinition(header.replace(id_, e), body.replace(id_, e))

    def handleOrdinary(self, handler):
        assert (templateStack.isEmpty())
        handler(self.header, self.body)

    def handleTemplated(self, handler):
        assert (templateStack.size() == 1)
        template = templateStack.top()
        id_ = template[0]
        exp_ = template[1]
        for e in exp_: handler(self.header, self.body, id_, e)
            
    def endElement(self, tag):
        if tag == "func":
            self.printTitle()
            if not templateStack.isEmpty():
                if filety == kDef: self.handleTemplated(self.defineTemplated)
                elif filety == kDecl: self.handleTemplated(self.declareTemplated)
                else: sys.exit()
            else:
                if filety == kDef: self.handleOrdinary(self.defineOrdinary)
                elif filety == kDecl: self.handleOrdinary(self.declareOrdinary)
                else: sys.exit()
        if tag == "template": templateStack.pop()     
        tagStack.pop()
            
    def characters(self, val):
        s = val.strip()
        if tagStack.top() == "body": self.body = s
        elif tagStack.top() == "header": self.header = s

#see: https://www.tutorialspoint.com/python/python_xml_processing.htm
parser = xml.sax.make_parser()
parser.setFeature(xml.sax.handler.feature_namespaces,0)
handler = TemplateHandler()
parser.setContentHandler(handler)
parser.parse(sys.stdin)
