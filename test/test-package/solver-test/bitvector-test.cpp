// CppUnit
# include <cppunit/extensions/HelperMacros.h>
# include <cppunit/TestFixture.h>
#include <cppunit/extensions/TestFactoryRegistry.h>
#include <cppunit/ui/text/TestRunner.h>

# include "src/solver/expr.hpp"
# include "src/solver/expr-factory.hpp"
# include "src/solver/bitvector-expr.hpp"

int main ()
{
  CppUnit::TextUi::TestRunner runner;
  CppUnit::TestFactoryRegistry &registry
    = CppUnit::TestFactoryRegistry::getRegistry();
  runner.addTest( registry.makeTest() );
  bool wasSucessful = runner.run( "", false );
  return wasSucessful;
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
    CPPUNIT_ASSERT (false);
  }
};

CPPUNIT_TEST_SUITE_REGISTRATION (BitvectorTest);
