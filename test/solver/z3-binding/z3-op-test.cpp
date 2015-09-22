// CppUnit
# include <cppunit/extensions/HelperMacros.h>
# include <cppunit/TestFixture.h>

// Target
# include "src/solver/z3-binding/z3-solver.hpp"
using solver::Z3Solver;

class Z3OpTest : public CppUnit::TestFixture
{

  CPPUNIT_TEST_SUITE (Z3OpTest);
  CPPUNIT_TEST (testAddition);
  CPPUNIT_TEST_SUITE_END ();

private:
  Z3Solver *solver = NULL;
  
public:
  void setUp ()
  {
    solver = new Z3Solver ();
  }
  
  void tearDown ()
  {
    delete solver;
  }
  
  void testAddition ()
  {
    
  }
};

