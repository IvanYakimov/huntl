// sort {1, 2, 3, 10} 4 :=> {1, 2, 3, 10}
// sort {0, 0, 1, 0} 4 :=> {0, 0, 0, 1}
// sort {4, 8, 8, 6} 4 :=> {4, 6, 8, 8}
// sort {6, 7, 9, 6} 4 :=> {6, 6, 7, 9}
// sort {-10, -9, -10, 7} 4 :=> {-10, -10, -9, 7}
// sort {6, 8, 6, 6} 4 :=> {6, 6, 6, 8}
// sort {-10, -1, -2, -4} 4 :=> {-10, -4, -2, -1}
// sort {-6, -6, -6, -8} 4 :=> {-8, -6, -6, -6}
// sort {-4, -4, 4, -10} 4 :=> {-10, -4, -4, 4}
// sort {-9, 6, 6, -10} 4 :=> {-10, -9, 6, 6}
// sort {5, 6, 9, 2} 4 :=> {2, 5, 6, 9}
// sort {6, 7, 6, -2} 4 :=> {-2, 6, 6, 7}
// sort {5, 7, 6, 0} 4 :=> {0, 5, 6, 7}
// sort {1, 1, 0, 1} 4 :=> {0, 1, 1, 1}
// sort {1, 1, -5, 0} 4 :=> {-5, 0, 1, 1}
// sort {-2, -1, -8, 9} 4 :=> {-8, -2, -1, 9}
// sort {-9, -1, -10, -9} 4 :=> {-10, -9, -9, -1}
// sort {3, 8, -2, 0} 4 :=> {-2, 0, 3, 8}
// sort {3, 3, 2, 0} 4 :=> {0, 2, 3, 3}
// sort {-2, -1, -3, -8} 4 :=> {-8, -3, -2, -1}
// sort {-2, -10, -2, 0} 4 :=> {-10, -2, -2, 0}
// sort {1, 0, 10, 9} 4 :=> {0, 1, 9, 10}
// sort {1, -2, 1, 0} 4 :=> {-2, 0, 1, 1}
// sort {-9, -10, 7, -10} 4 :=> {-10, -10, -9, 7}
// sort {3, -10, 2, 3} 4 :=> {-10, 2, 3, 3}
// sort {-9, -10, -10, -10} 4 :=> {-10, -10, -10, -9}
// sort {-2, -8, -6, -8} 4 :=> {-8, -8, -6, -2}
// sort {2, -9, -2, -10} 4 :=> {-10, -9, -2, 2}
// sort {-2, -7, 0, -8} 4 :=> {-8, -7, -2, 0}
// sort {2, 1, -4, 2} 4 :=> {-4, 1, 2, 2}
// sort {1, 0, -8, 0} 4 :=> {-8, 0, 0, 1}
// sort {6, 3, -7, 0} 4 :=> {-7, 0, 3, 6}
// sort {-1, -2, -7, -8} 4 :=> {-8, -7, -2, -1}
//parsed
void runner0()
{
	char arg1[] = {1, 2, 3, 10};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner1()
{
	char arg1[] = {0, 0, 1, 0};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner2()
{
	char arg1[] = {4, 8, 8, 6};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner3()
{
	char arg1[] = {6, 7, 9, 6};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner4()
{
	char arg1[] = {-10, -9, -10, 7};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner5()
{
	char arg1[] = {6, 8, 6, 6};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner6()
{
	char arg1[] = {-10, -1, -2, -4};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner7()
{
	char arg1[] = {-6, -6, -6, -8};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner8()
{
	char arg1[] = {-4, -4, 4, -10};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner9()
{
	char arg1[] = {-9, 6, 6, -10};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner10()
{
	char arg1[] = {5, 6, 9, 2};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner11()
{
	char arg1[] = {6, 7, 6, -2};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner12()
{
	char arg1[] = {5, 7, 6, 0};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner13()
{
	char arg1[] = {1, 1, 0, 1};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner14()
{
	char arg1[] = {1, 1, -5, 0};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner15()
{
	char arg1[] = {-2, -1, -8, 9};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner16()
{
	char arg1[] = {-9, -1, -10, -9};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner17()
{
	char arg1[] = {3, 8, -2, 0};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner18()
{
	char arg1[] = {3, 3, 2, 0};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner19()
{
	char arg1[] = {-2, -1, -3, -8};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner20()
{
	char arg1[] = {-2, -10, -2, 0};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner21()
{
	char arg1[] = {1, 0, 10, 9};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner22()
{
	char arg1[] = {1, -2, 1, 0};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner23()
{
	char arg1[] = {-9, -10, 7, -10};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner24()
{
	char arg1[] = {3, -10, 2, 3};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner25()
{
	char arg1[] = {-9, -10, -10, -10};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner26()
{
	char arg1[] = {-2, -8, -6, -8};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner27()
{
	char arg1[] = {2, -9, -2, -10};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner28()
{
	char arg1[] = {-2, -7, 0, -8};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner29()
{
	char arg1[] = {2, 1, -4, 2};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner30()
{
	char arg1[] = {1, 0, -8, 0};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner31()
{
	char arg1[] = {6, 3, -7, 0};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner32()
{
	char arg1[] = {-1, -2, -7, -8};
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
}
//generated
