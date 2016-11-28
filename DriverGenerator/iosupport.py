def openFile(name, mode):
    try:
        result = open(name, mode)
        return result
    except IOError:
        print "IO error while opening the file", name, "in", mode, "mode"
        sys.exit(errno.EIO)
