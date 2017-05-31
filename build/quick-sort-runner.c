// sort {6, 6, -8, 6} 4 :=> {-8, 6, 6, 6}
// sort {6, 0, -8, 0} 4 :=> {-8, 0, 0, 6}
// sort {0, 0, -8, -8} 4 :=> {-8, -8, 0, 0}
// sort {7, 6, -8, -2} 4 :=> {-8, -2, 6, 7}
// sort {-10, -8, -10, -10} 4 :=> {-10, -10, -10, -8}
// sort {-2, -8, -8, -4} 4 :=> {-8, -8, -4, -2}
// sort {-2, -10, -9, -9} 4 :=> {-10, -9, -9, -2}
// sort {-2, -9, -10, -2} 4 :=> {-10, -9, -2, -2}
// sort {6, -10, 6, -10} 4 :=> {-10, -10, 6, 6}
// sort {6, -10, 7, -2} 4 :=> {-10, -2, 6, 7}
// sort {6, -10, 3, -10} 4 :=> {-10, -10, 3, 6}
// sort {-10, 6, 6, -10} 4 :=> {-10, -10, 6, 6}
// sort {-9, -1, 6, -9} 4 :=> {-9, -9, -1, 6}
// sort {-10, 8, 2, -10} 4 :=> {-10, -10, 2, 8}
// sort {7, 7, 6, -10} 4 :=> {-10, 6, 7, 7}
// sort {6, 6, 7, -10} 4 :=> {-10, 6, 6, 7}
// sort {6, 7, 7, -10} 4 :=> {-10, 6, 7, 7}
// sort {4, 6, 7, -10} 4 :=> {-10, 4, 6, 7}
// sort {-9, 0, -8, -10} 4 :=> {-10, -9, -8, 0}
// sort {6, -2, 6, -10} 4 :=> {-10, -2, 6, 6}
// sort {6, -9, 7, -10} 4 :=> {-10, -9, 6, 7}
// sort {9, 8, 8, 0} 4 :=> {0, 8, 8, 9}
// sort {10, 7, 6, -7} 4 :=> {-7, 6, 7, 10}
// sort {7, -9, 6, -10} 4 :=> {-10, -9, 6, 7}
// sort {6, 7, 6, 7} 4 :=> {6, 6, 7, 7}
// sort {6, 7, -10, 7} 4 :=> {-10, 6, 7, 7}
// sort {-2, 6, 0, 0} 4 :=> {-2, 0, 0, 6}
// sort {-6, -1, 7, -1} 4 :=> {-6, -1, -1, 7}
// sort {0, 10, 10, 8} 4 :=> {0, 8, 10, 10}
// sort {-10, -1, 8, -9} 4 :=> {-10, -9, -1, 8}
// sort {-6, 8, 2, -5} 4 :=> {-6, -5, 2, 8}
// sort {-4, -4, -2, -2} 4 :=> {-4, -4, -2, -2}
// sort {3, -6, 7, 7} 4 :=> {-6, 3, 7, 7}
// sort {-10, -4, 2, 2} 4 :=> {-10, -4, 2, 2}
// sort {-8, -8, 4, -4} 4 :=> {-8, -8, -4, 4}
// sort {-9, -10, 6, -1} 4 :=> {-10, -9, -1, 6}
// sort {-2, 0, 9, 8} 4 :=> {-2, 0, 8, 9}
// sort {-4, -9, -8, -3} 4 :=> {-9, -8, -4, -3}
// sort {0, 1, 0, 8} 4 :=> {0, 0, 1, 8}
// sort {2, 2, -3, 5} 4 :=> {-3, 2, 2, 5}
// sort {-3, -2, -4, -1} 4 :=> {-4, -3, -2, -1}
// sort {-2, -3, -4, -1} 4 :=> {-4, -3, -2, -1}
// sort {-10, -8, -8, -4} 4 :=> {-10, -8, -8, -4}
// sort {-10, -7, -8, -1} 4 :=> {-10, -8, -7, -1}
// sort {-10, -10, -6, -1} 4 :=> {-10, -10, -6, -1}
// sort {-7, -8, -6, -5} 4 :=> {-8, -7, -6, -5}
// sort {4, 8, 9, 10} 4 :=> {4, 8, 9, 10}
//parsed
void runner0()
{
	char arg1[] = {6, 6, -8, 6};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner1()
{
	char arg1[] = {6, 0, -8, 0};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner2()
{
	char arg1[] = {0, 0, -8, -8};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner3()
{
	char arg1[] = {7, 6, -8, -2};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner4()
{
	char arg1[] = {-10, -8, -10, -10};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner5()
{
	char arg1[] = {-2, -8, -8, -4};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner6()
{
	char arg1[] = {-2, -10, -9, -9};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner7()
{
	char arg1[] = {-2, -9, -10, -2};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner8()
{
	char arg1[] = {6, -10, 6, -10};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner9()
{
	char arg1[] = {6, -10, 7, -2};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner10()
{
	char arg1[] = {6, -10, 3, -10};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner11()
{
	char arg1[] = {-10, 6, 6, -10};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner12()
{
	char arg1[] = {-9, -1, 6, -9};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner13()
{
	char arg1[] = {-10, 8, 2, -10};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner14()
{
	char arg1[] = {7, 7, 6, -10};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner15()
{
	char arg1[] = {6, 6, 7, -10};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner16()
{
	char arg1[] = {6, 7, 7, -10};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner17()
{
	char arg1[] = {4, 6, 7, -10};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner18()
{
	char arg1[] = {-9, 0, -8, -10};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner19()
{
	char arg1[] = {6, -2, 6, -10};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner20()
{
	char arg1[] = {6, -9, 7, -10};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner21()
{
	char arg1[] = {9, 8, 8, 0};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner22()
{
	char arg1[] = {10, 7, 6, -7};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner23()
{
	char arg1[] = {7, -9, 6, -10};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner24()
{
	char arg1[] = {6, 7, 6, 7};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner25()
{
	char arg1[] = {6, 7, -10, 7};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner26()
{
	char arg1[] = {-2, 6, 0, 0};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner27()
{
	char arg1[] = {-6, -1, 7, -1};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner28()
{
	char arg1[] = {0, 10, 10, 8};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner29()
{
	char arg1[] = {-10, -1, 8, -9};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner30()
{
	char arg1[] = {-6, 8, 2, -5};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner31()
{
	char arg1[] = {-4, -4, -2, -2};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner32()
{
	char arg1[] = {3, -6, 7, 7};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner33()
{
	char arg1[] = {-10, -4, 2, 2};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner34()
{
	char arg1[] = {-8, -8, 4, -4};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner35()
{
	char arg1[] = {-9, -10, 6, -1};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner36()
{
	char arg1[] = {-2, 0, 9, 8};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner37()
{
	char arg1[] = {-4, -9, -8, -3};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner38()
{
	char arg1[] = {0, 1, 0, 8};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner39()
{
	char arg1[] = {2, 2, -3, 5};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner40()
{
	char arg1[] = {-3, -2, -4, -1};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner41()
{
	char arg1[] = {-2, -3, -4, -1};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner42()
{
	char arg1[] = {-10, -8, -8, -4};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner43()
{
	char arg1[] = {-10, -7, -8, -1};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner44()
{
	char arg1[] = {-10, -10, -6, -1};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner45()
{
	char arg1[] = {-7, -8, -6, -5};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner46()
{
	char arg1[] = {4, 8, 9, 10};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
int main(){
	runner0();
	runner1();
	runner2();
	runner3();
	runner4();
	runner5();
	runner6();
	runner7();
	runner8();
	runner9();
	runner10();
	runner11();
	runner12();
	runner13();
	runner14();
	runner15();
	runner16();
	runner17();
	runner18();
	runner19();
	runner20();
	runner21();
	runner22();
	runner23();
	runner24();
	runner25();
	runner26();
	runner27();
	runner28();
	runner29();
	runner30();
	runner31();
	runner32();
	runner33();
	runner34();
	runner35();
	runner36();
	runner37();
	runner38();
	runner39();
	runner40();
	runner41();
	runner42();
	runner43();
	runner44();
	runner45();
	runner46();
}
//generated
