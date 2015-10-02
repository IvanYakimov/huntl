// CppUnit
# include <cppunit/extensions/HelperMacros.h>
# include <cppunit/TestFixture.h>

# include "src/solver/expr.hpp"
# include "src/solver/expr-factory.hpp"
# include "src/solver/bitvector-expr.hpp"

int main ()
{
  
}

class BitvectorTest : public CppUnit::TestFixture
{
private:
  CPPUNIT_TEST_SUITE (BitvectorTest);
  CPPUNIT_TEST (testConst);
  CPPUNIT_TEST_SUITE_END ();

public:
  void setUp ()
  {
  }

  void tearDown ()
  {
  }
  
  void testConst ()
  {
  }
};
