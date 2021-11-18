#include "SAT.h"

#define LOG(x) std::cout << x << std::endl;

using namespace std;

string SAT_vertex::path = "";
unsigned int SAT_vertex::initial_configuration = 0;
bool SAT_vertex::Active_ReadWrite_access = false;
unsigned int SAT_vertex::no_CSUs = 0;
bool SAT_vertex::optimal_solution = false;
bool SAT_vertex::retarget_all_TDRs = false;


/*
https://www.geeksforgeeks.org/command-line-arguments-in-c-cpp/
Properties of Command Line Arguments :
*	They are passed to main() function.
*	They are parameters / arguments supplied to the program when it is invoked.
*	They are used to control program from outside instead of hard coding those values inside the code.
*	argv[argc] is a NULL pointer.
*	argv[0] holds the name of the program.
*	argv[1] points to the first command line argument and argv[n] points last argument.
*/

//int main(int argc, char** argv) //https://www.tutorialspoint.com/cprogramming/c_command_line_arguments.htmargc 
int main()
{
	measurements solver_return;
	//argc: refers to the number of arguments passed, and argv[]: is a pointer array which points to each argument passed to the program
	printf("Please Enter the required parameters with the following order: \n");
	printf("{path, initial_conf, write_read, UB-CSUs, Optimal_First, test_all_TDRs} \n");
	
	unsigned int CSU_upperBound;
	double avg_execution_time = 0, avg_n_conflicts = 0;
	unsigned int no_readings = 3;

	char *inputs[] = { "", "./../../UpperBound_Benchmarks/Fig3/", "0", "0", "5", "1", "0" }; //{path, initial_conf, Active_ReadWrite, UB-CSUs, Optimal_First, test_all_TDRs} 
	char** argv = inputs;
	
	//this section is to set class's static variables.
	SAT_vertex::path = argv[1];
	SAT_vertex::initial_configuration = stoi(argv[2]);
	SAT_vertex::Active_ReadWrite_access = stoi(argv[3]) ;
	SAT_vertex::no_CSUs = stoi(argv[4]);
	SAT_vertex::optimal_solution = stoi(argv[5]);
	SAT_vertex::retarget_all_TDRs = stoi(argv[6]);
	
	//for (unsigned int reading = 0; reading < no_readings; reading++) //we need to take the average of five readings:
	{
		SAT_vertex root;
		solver_return = root.apply_SAT_retargeting();
		
		avg_execution_time += solver_return.execution_time;
		avg_n_conflicts += solver_return.n_conflicts;
		
		root.~SAT_vertex();
	}
	//printf("The Average execution time = %f s\n", avg_execution_time / no_readings);
	//printf("The Average No. of Conflicts = %f s\n", max_n_conflicts / no_readings);


	char x;
	printf("please enter a char to exit");
	scanf("%c", &x);
	
	return 0;
}