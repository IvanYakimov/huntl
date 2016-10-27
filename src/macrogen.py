#!/usr/bin/env python
import fileinput
import sys
#see: https://www.tutorialspoint.com/python/python_xml_processing.htm
import xml.sax

filety = 0
kDecl = 1
kDef = 2
argnum = len(sys.argv)

def argsWarning():
    print "wrong number of arguments, use --decl of --def"
    sys.exit()

if argnum  == 1:
    argsWarning()
elif argnum == 2:
    arg1 = sys.argv[1]
    if arg1 == "--decl":
       filety = kDecl
    elif arg1 == "--def":
        filety = kDef
    else:
        argsWarning()
else:
    argsWarning()
    
# see: https://interactivepython.org/runestone/static/pythonds/BasicDS/ImplementingaStackinPython.html
class Stack:
     def __init__(self):
         self.items = []
     def isEmpty(self):
         return self.items == []
     def push(self, item):
         self.items.append(item)
     def pop(self):
         return self.items.pop()
     def top(self):
         return self.items[len(self.items)-1]
     def size(self):
         return len(self.items)
    
tagStack = Stack()
templateStack = Stack()

# parser
class TemplateHandler (xml.sax.ContentHandler):
    def __init__(self):
        key = ""

    def startElement(self, tag, atts):
        tagStack.push(tag)
        if tag == "func":
            self.name = atts["name"].strip()
        elif tag == "template":
            id_ = atts["id"].strip()
            exp = atts["exp"].strip().split()
            templateStack.push((id_, exp))

    def title(self):
        print "\t//" + self.name

    def declare(self):
        assert (templateStack.isEmpty())
        print "\t" + self.header + ";"

    def define(self):
        assert (templateStack.isEmpty())
        print "\t" + self.header + " {"
        print "\t\t" + self.body + "\n\t}\n"

    def handleTemplated(self):
        assert (templateStack.size() == 1)

    def declare_templated(self):
        assert (templateStack.size() == 1)
        template = templateStack.top()
        id_ = template[0]
        exp_ = template[1]
        for e in exp_:
            print "\t" + self.header.replace(id_, e) + ";"
            
    def define_templated(self):
        assert (templateStack.size() == 1)
        template = templateStack.top()
        id_ = template[0]
        exp_ = template[1]
        for e in exp_:
            print "\t" + self.header.replace(id_, e) + " {"
            print "\t\t" + self.body.replace(id_, e) + "\n\t}\n"
            
    def endElement(self, tag):
        if tag == "func":
            self.title()
            if not templateStack.isEmpty():
                if filety == kDef:
                    self.define_templated()
                elif filety == kDecl:
                    self.declare_templated()
                else:
                    sys.exit()
            else:
                if filety == kDef:
                    self.define()
                elif filety == kDecl:
                    self.declare()
                else:
                    sys.exit()
        if tag == "template":
           templateStack.pop()     
        tagStack.pop()
            
    def characters(self, val):
        s = val.strip()
        if tagStack.top() == "body":
            self.body = s
        elif tagStack.top() == "header":
            self.header = s
            
parser = xml.sax.make_parser()
parser.setFeature(xml.sax.handler.feature_namespaces,0)
handler = TemplateHandler()
parser.setContentHandler(handler)
parser.parse(sys.stdin)
