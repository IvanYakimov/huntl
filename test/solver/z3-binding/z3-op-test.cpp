# include <cppunit/extensions/HelperMacros.h>

// http://c2.com/cgi/wiki?DirtSimpleCppUnitExample

class Z3OpTest : public CppUnit::TestFixture
{  
  CPPUNIT_TEST_SUITE (Z3OpTest);
  CPPUNIT_TEST (testAddition);

  static CppUnit::TestSuite *suite ();
  
private:
  
public:
  void setUp ()
  {
  }
  void tearDown ()
  {
  }
  void testAddition ()
  {
  }
};

