// sort {6, 6, 6, 6} 4 :=> {6, 6, 6, 6}
// sort {2, 4, 6, 4} 4 :=> {2, 4, 4, 6}
// sort {6, 7, 7, 6} 4 :=> {6, 6, 7, 7}
// sort {-6, -6, -6, -10} 4 :=> {-10, -6, -6, -6}
// sort {4, 5, 4, 5} 4 :=> {4, 4, 5, 5}
// sort {1, 2, -8, 2} 4 :=> {-8, 1, 2, 2}
// sort {-8, 9, -7, 8} 4 :=> {-8, -7, 8, 9}
// sort {4, 8, 7, 6} 4 :=> {4, 6, 7, 8}
// sort {-2, -1, -2, -8} 4 :=> {-8, -2, -2, -1}
// sort {-9, 3, -10, 1} 4 :=> {-10, -9, 1, 3}
// sort {9, 10, 6, 6} 4 :=> {6, 6, 9, 10}
// sort {8, 8, -4, -10} 4 :=> {-10, -4, 8, 8}
// sort {6, -10, 6, 8} 4 :=> {-10, 6, 6, 8}
// sort {1, 0, 10, 4} 4 :=> {0, 1, 4, 10}
// sort {1, 0, 2, 0} 4 :=> {0, 0, 1, 2}
// sort {10, 8, 10, -10} 4 :=> {-10, 8, 10, 10}
// sort {10, -8, 2, 10} 4 :=> {-8, 2, 10, 10}
// sort {-8, -9, -10, 8} 4 :=> {-10, -9, -8, 8}
// sort {8, 0, 0, 0} 4 :=> {0, 0, 0, 8}
// sort {2, -10, -3, -4} 4 :=> {-10, -4, -3, 2}
// sort {-5, -7, -7, -8} 4 :=> {-8, -7, -7, -5}
// sort {3, 1, 0, 2} 4 :=> {0, 1, 2, 3}
// sort {-1, -2, -4, -4} 4 :=> {-4, -4, -2, -1}
// sort {8, 4, -8, -10} 4 :=> {-10, -8, 4, 8}
//parsed
void runner0()
{
	char arg1[] = {6, 6, 6, 6};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner1()
{
	char arg1[] = {2, 4, 6, 4};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner2()
{
	char arg1[] = {6, 7, 7, 6};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner3()
{
	char arg1[] = {-6, -6, -6, -10};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner4()
{
	char arg1[] = {4, 5, 4, 5};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner5()
{
	char arg1[] = {1, 2, -8, 2};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner6()
{
	char arg1[] = {-8, 9, -7, 8};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner7()
{
	char arg1[] = {4, 8, 7, 6};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner8()
{
	char arg1[] = {-2, -1, -2, -8};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner9()
{
	char arg1[] = {-9, 3, -10, 1};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner10()
{
	char arg1[] = {9, 10, 6, 6};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner11()
{
	char arg1[] = {8, 8, -4, -10};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner12()
{
	char arg1[] = {6, -10, 6, 8};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner13()
{
	char arg1[] = {1, 0, 10, 4};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner14()
{
	char arg1[] = {1, 0, 2, 0};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner15()
{
	char arg1[] = {10, 8, 10, -10};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner16()
{
	char arg1[] = {10, -8, 2, 10};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner17()
{
	char arg1[] = {-8, -9, -10, 8};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner18()
{
	char arg1[] = {8, 0, 0, 0};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner19()
{
	char arg1[] = {2, -10, -3, -4};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner20()
{
	char arg1[] = {-5, -7, -7, -8};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner21()
{
	char arg1[] = {3, 1, 0, 2};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner22()
{
	char arg1[] = {-1, -2, -4, -4};
	int arg2 = 4;
	char *res = NULL;
	res = sort(arg1, arg2);
}
void runner23()
{
	char arg1[] = {8, 4, -8, -10};
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
}
//generated
