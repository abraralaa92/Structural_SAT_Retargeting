#pragma once
#include <string>  // // std::string, std::stoi
#include <vector>
#include <algorithm> //The C++ STL contains the function std::count(). To use this function, we have to use either <bits/stdc++> header or <algorithm> header.
#include <sstream>  //for file read and write 
#include <fstream>
#include <chrono> //used for the generation of the execution time

#include <signal.h>
#ifdef _MSC_VER 
#include <win7/zlib.h> 
#else 
#   include <zlib.h> 
#   include <sys/resource.h> 
#endif 

#include "minisat/utils/System.h"
#include "minisat/utils/ParseUtils.h"
#include "minisat/utils/Options.h"
#include "minisat/core/Dimacs.h"
#include "minisat/simp/SimpSolver.h"

using namespace Minisat;
using namespace std;

static Solver* solver; //This is for the MiniSAT solver

enum _Type
{
	NW_Vertices,
	NW_Clauses,
	NW_SelDepGraph,
	NW_SMV,
	NW_Graph,
	NW_Instruments
};

struct _clause
{
	string clause;
	int state; //int and not bool because we could have SCBs with more than 1 bit also Network shift_registers like (TDRs) are multi_bits, also not unsigned int because we may need to use (-1) for unknown states like TDRs initial states or TDRs dummy_value when the TDR is part of the ASP but not the target_reg.

	_clause(const string& a, const unsigned int& b)     //this constructor to be used with emplace_back for pushing a struct into a vector
		: clause(a), state(b)
	{
		//printf("Clause constructed!!\n");
	}

	_clause(const _clause& x)
		:clause(x.clause), state(x.state)
	{
		printf("Clause copied!!\n");
	}/*
	~_clause()
	{
		printf("Clause destructed!!\n");
	}
	*/
};

void split_selection_clause_into_vectorOfClauses(const string& selection_clause, vector<_clause>& output_vector); //I need to define the method here, and write the implementation below, where it have to be defined before using it in the following constructor, otherwise, an (identifier not found) error will be produced!!
struct _selection_clause
{
	string id;
	vector<_clause> clause; //"_": to differentiate between struct clause and string clause
	unsigned int length;
	unsigned int reset_value;

	_selection_clause(const string& a, const unsigned int& b, const unsigned int& c, const string& selection_clause)     //this constructor to be used with emplace_back for pushing a struct element into a vector. We removed (const vector<clause>& b) from constructor's defenition because (_clause) will be accessed and updated seperately through (split_selection_clause_into_vectorOfClauses) method, so no need to pass it to the constructor.
		: id(a), length(b), reset_value(c)
	{
		split_selection_clause_into_vectorOfClauses(selection_clause, clause);
	}

	_selection_clause(const _selection_clause& x)
		:id(x.id), clause(x.clause), length(x.length), reset_value(x.reset_value)
	{
		printf("selection_clause copied!!\n");
	}/*
	~_selection_clause()
	{
		printf("selection_clause Distructed!!\n");
	}
	*/
};

struct _SDG
{
	string id;
	string successors;  //successor in SDG is the predecessor in NW-connection
	string address_control_bit;
	unsigned int length;

	_SDG(const string& a, const string &b, const string& c, const unsigned int& d)
		: id(a), successors(b), address_control_bit(c), length(d) {}
	/*
	_SDG(const _SDG& x)
		: id(x.id), successors(x.successors), address_control_bit(x.address_control_bit), length(x.length)
	{
		printf("SDG copied!!\n");
	}
	~_SDG()
	{
		printf("SDG Distructed!!\n");
	}
	*/
};

struct _smv
{
	string id;
	string predecessors; //or (SUC/MUX/ShiftRegister) modules' inputs
	string type; //SUC, MUX, ShiftRegister_10
	string address_control_bit;
	string selectControlInput;

	_smv(const string& a, const string &b, const string& c, const string& d, const string& e)
		: id(a), predecessors(b), type(c), address_control_bit(d), selectControlInput(e) {}
	/*
	_smv(const _smv& x)
		: id(x.id), predecessors(x.predecessors), type(x.type), address_control_bit(x.address_control_bit), selectControlInput(x.selectControlInput)
	{
		printf("smv copied!!\n");
	}
	~_smv()
	{
		printf("smv Distructed!!\n");
	}
	*/
};

struct _graph
{
	string id;
	string selection_clause;
	string address_control_bit;
	unsigned int length;
	vector <string> predecessors; //we need both predecessor and successor pointers for SAT to check (SP_SS, SP_MS, MP_SS, MP_MS), (S,M,P,S): (single, multiple, predecesssor, successor) 
	vector <string> successors; //<unsigned int> these vector carry the Indices of successor and predeccor vertices; The trouble with using vector<vertex*> is that, whenever the vector goes out of scope unexpectedly(like when an exception is thrown), the vector cleans up after yourself, but this will only free the memory it manages for holding the pointer, not the memory you allocated for what the pointers are referring to.(https://stackoverflow.com/questions/1361139/how-to-avoid-memory-leaks-when-using-a-vector-of-pointers-to-dynamically-allocat/1361227)
	
	_graph(const string &a, const string &b, const string &c, unsigned int d)
		: id(a), selection_clause(b), address_control_bit(c), length(d) {}

	_graph(const _graph& x)
		: id(x.id), selection_clause(x.selection_clause), address_control_bit(x.address_control_bit), length(x.length), predecessors(x.predecessors), successors(x.successors)
	{
		printf("graph copied!!\n");
	}/*
	~_graph()
	{
		printf("graph Distructed!!\n");
	}
	*/
};

struct _SAT_variable
{
	string id;
	unsigned int timeFrame;
	unsigned int type; //SCT class: 1 for SCB.state (value). 2 for SCB.initialized (flag). 3 for SCB.TSatisfied (flag), Target-Satisfied flag. SAT class: 1 for the "state" of the address control bit of the multiplexers. 2 for the "select" control input of the scan segments. 
	unsigned int SAT_no; // SATvariable_no, each vertex in the network (NW_SAT_predicates: stateElements and AUX, control and address inputs: sel(SR) and (SR)) will be assigned a SAT variable NUMBER after calling (assign_index_to_SATvertices) method to be passed to the SAT solver
	bool SAT_assignment; //We set its value in the constructor to (false) as some initial value until it would be solved and assigned the correct assignment by the SAT solver
	
	bool operator==(string const &i) //will be needed inside the 'find' method, otherwise this error will be generated "binary '==': no operator found which takes a left hand operand of type 'SAT_variable' .. "
	{
		return (id == i);
	}

	_SAT_variable(const string& a, const unsigned int& b, const unsigned int& c, const unsigned int& d, const bool& e = false) //in (type) argument wee set its default value to true which is the case in SCT_to_SAT model since all SAT_variables are "state" varaiables and no "select" variables are used.
		: id(a), timeFrame(b), type(c), SAT_no(d), SAT_assignment(e) {}

	_SAT_variable(const _SAT_variable& x)
		: id(x.id), timeFrame(x.timeFrame), type(x.type), SAT_no(x.SAT_no), SAT_assignment(x.SAT_assignment)
	{
		printf("SAT_variable copied!!\n");
	}/*
	~_SAT_variable()
	{
		printf("SAT_variable Distructed!!\n");
	}
	*/
};

enum _SAT_Type
{
	SAT_clauses,
	SAT_retargeting_vectors
};

struct _SAT_literal
{
	string id;
	unsigned int timeFrame; //(id, timeFrame, type) is the primary key
	unsigned int type; //in SCT class: 1 for SCB.state (value). 2 for SCB.initialized (flag). 3 for SCB.TSatisfied (flag)/Target-Satisfied flag. in SAT class: 1 for the "state" of the address control bit of the multiplexers. 2 for the "select" control input of the scan segments. 
	unsigned int state; //True means: (state(SR)=1) or (sel(SR)), False means negated: (state(SR)=0) or (!sel(SR)). //unsigned int: to add more flexibility, where network's SCBs may consists of more than one bit, which could hold different states values. for ex, for [0 --> 2^#bits], I coulf have different state: (0, 1, 2, 3)

	_SAT_literal(const string& a, unsigned int b, unsigned int c, unsigned int d)
		:id(a), timeFrame(b), type(c), state(d) {}

	_SAT_literal(const _SAT_literal& x)
		: id(x.id), timeFrame(x.timeFrame), type(x.type), state(x.state)
	{
		printf("SAT_literal copied!!\n");
	}/*
	~_SAT_literal()
	{
		printf("SAT_literal Distructed!!\n");
	}
	*/
};

struct _SAT_predicate
{
	vector<_SAT_literal> SAT_literals; //vector of ORed literals for SAT retargeting

	_SAT_predicate(const string& a, unsigned int b, unsigned int c, unsigned int d)
	{
		SAT_literals.emplace_back(a, b, c, d);
	}

	_SAT_predicate(unsigned int no_literals)
	{
		SAT_literals.reserve(no_literals);
	}

	_SAT_predicate(const _SAT_predicate& x)
		: SAT_literals(x.SAT_literals)
	{
		printf("SAT predicate copied!!\n");
	}

	~_SAT_predicate()
	{
		//printf("SAT predicate Distructed!!\n");
		std::vector<_SAT_literal>().swap(SAT_literals);
	}
};

struct measurements
{
	string satisfiable_string;	//used to hold the satisfable_string generated by the MiniSAT solver in case that the SAT instance is SATISFIABLE.
	double execution_time;
	unsigned int n_conflicts; //here the data type should be something similar to (unsigned int), however, we are making it souble to make this structor applicable for differnet uses, like (Avg execution_time, Max execution_time)
	unsigned int AccessTime; //Access time (CC)
	unsigned int no_CSUs; //number of CSUs

	measurements()
		:satisfiable_string(""), execution_time(0), n_conflicts(0), AccessTime(0), no_CSUs(0){}
	measurements(double a, unsigned int b, unsigned int c)
		: satisfiable_string(""), execution_time(a), n_conflicts(b), AccessTime(c), no_CSUs(0) {}
	measurements(const measurements& x)
		: satisfiable_string(x.satisfiable_string), execution_time(x.execution_time), n_conflicts(x.n_conflicts), AccessTime (x.AccessTime), no_CSUs(x.no_CSUs)
	{
		//printf("measurements copied!!\n");
	}
};

struct NWElement_statistics
{
	string reg_id;
	unsigned int n_SAT_variables = 0;
	unsigned int n_SAT_clauses = 0;
	vector <measurements> solver_returns;	//this vector saves all possible retargeting solutions along with every silution's cost. we used vector<_clause> only for its data type convenience. Where string(clause) data member is used to save satisfiable_string and int(state) is used to save this solution cost.

	NWElement_statistics(const string& a)
		: reg_id(a) {}
	NWElement_statistics(const NWElement_statistics& x)
		: reg_id(x.reg_id), n_SAT_variables(x.n_SAT_variables), n_SAT_clauses(x.n_SAT_clauses), solver_returns(x.solver_returns)
	{
		printf("NWElement_statistics copied!!\n");
	}
	~NWElement_statistics()
	{
		vector<measurements>().swap(solver_returns);
	}
};

inline int myPow(int x, int p) {
	if (p == 0) return 1;
	if (p == 1) return x;
	return x * myPow(x, p - 1);
}

inline std::string trim(const std::string& line)
{
	const char* WhiteSpace = " \t\v\r\n";
	std::size_t start = line.find_first_not_of(WhiteSpace);
	std::size_t end = line.find_last_not_of(WhiteSpace);
	return start == end ? std::string() : line.substr(start, end - start + 1);
}

inline void printStats(Solver& solver)
{
	double cpu_time = cpuTime();
	double mem_used = memUsedPeak();
	printf("restarts              : %-12lld\n", solver.starts);
	printf("conflicts             : %-12lld   (%.0f /sec)\n",
		solver.conflicts, solver.conflicts / cpu_time);
	printf("decisions             : %-12lld   (%4.2f %% random) (%.0f /sec)\n", solver.decisions, (float)solver.rnd_decisions * 100 /
		(float)solver.decisions, solver.decisions / cpu_time);
	printf("propagations          : %-12lld   (%.0f /sec)\n",
		solver.propagations, solver.propagations / cpu_time);
	printf("conflict literals     : %-12lld   (%4.2f %% deleted)\n",
		solver.tot_literals, (solver.max_literals - solver.tot_literals) * 100 /
		(double)solver.max_literals);
	if (mem_used != 0) printf("Memory used           : %.2f MB\n",
		mem_used);
	printf("CPU time              : %g s\n", cpu_time);
}

inline void run_SAT_solver(const string& input_file, measurements& output_satisfiable_solution) //output_satisfiable_string can't be passed as const string: expression must be a modifiable value. Why (inline function)? https://docs.microsoft.com/en-us/cpp/error-messages/tool-errors/linker-tools-error-lnk2005?f1url=https%3A%2F%2Fmsdn.microsoft.com%2Fquery%2Fdev15.query%3FappId%3DDev15IDEF1%26l%3DEN-US%26k%3Dk(LNK2005)%26rd%3Dtrue&view=vs-2019
{
	auto start = std::chrono::high_resolution_clock::now();

	// Extra options:
	IntOption    verb("MAIN", "verb", "Verbosity level (0=silent, 1=some, 2=more).", 1, IntRange(0, 2));
	BoolOption   pre("MAIN", "pre", "Completely turn on/off any preprocessing.", true);
	StringOption dimacs("MAIN", "dimacs", "If given, stop after preprocessing and write the result to this file.");
	IntOption    cpu_lim("MAIN", "cpu-lim", "Limit on CPU time allowed in seconds.\n", INT32_MAX, IntRange(0, INT32_MAX));
	IntOption    mem_lim("MAIN", "mem-lim", "Limit on memory usage in megabytes.\n", INT32_MAX, IntRange(0, INT32_MAX));

	SimpSolver  S;
	double initial_time = cpuTime();

	if (!pre) S.eliminate(true);

	S.verbosity = verb;

	solver = &S;
	gzFile in = NULL;
	in = gzopen(input_file.c_str(), "rb"); //in = gzopen("input.txt", "rb");

	//gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
	if (in == NULL)
		printf("ERROR! Could not open file: %s\n", input_file.c_str()), exit(1);

	if (S.verbosity > 0) {
		printf("============================[ Problem Statistics ]=============================\n");
		printf("|                                                                             |\n");
	}

	parse_DIMACS(in, S);
	gzclose(in);

	if (S.verbosity > 0) {
		printf("|  Number of variables:  %12d                                         |\n", S.nVars());
		printf("|  Number of clauses:    %12d                                         |\n", S.nClauses());
	}

	double parsed_time = cpuTime();
	if (S.verbosity > 0)
		printf("|  Parse time:           %12.2f s                                       |\n", parsed_time - initial_time);

	S.eliminate(true);
	double simplified_time = cpuTime();
	if (S.verbosity > 0) {
		printf("|  Simplification time:  %12.2f s                                       |\n", simplified_time - parsed_time);
		printf("|                                                                             |\n");
	}

	vec<Lit> dummy;
	lbool ret = S.solveLimited(dummy);   //calling the solver
	auto elapsed = std::chrono::steady_clock::now() - start;

	if (S.verbosity > 0) {
		printStats(S);
		printf("\n");
	}
	printf(ret == l_True ? "SATISFIABLE\n" : ret == l_False ? "UNSATISFIABLE\n" : "INDETERMINATE\n");

	if (ret == l_True) {
		for (int i = 0; i < S.nVars(); i++)
			if (S.model[i] != l_Undef)
			{
				output_satisfiable_solution.satisfiable_string += (i == 0) ? "" : " ";
				output_satisfiable_solution.satisfiable_string += (S.model[i] == l_True) ? "" : "-";
				output_satisfiable_solution.satisfiable_string += to_string(i + 1);
			}
	}

	//set the cpu, conflicts measurements to be used later in get_avg(), get_max()
	output_satisfiable_solution.execution_time = std::chrono::duration<double>(elapsed).count(); //the units is (sec).
	output_satisfiable_solution.n_conflicts = S.conflicts;
}

inline void run_SAT_solver_withNoPrint(const string& input_file, measurements& output_satisfiable_solution) //output_satisfiable_string can't be passed as const string: expression must be a modifiable value. Why (inline function)? https://docs.microsoft.com/en-us/cpp/error-messages/tool-errors/linker-tools-error-lnk2005?f1url=https%3A%2F%2Fmsdn.microsoft.com%2Fquery%2Fdev15.query%3FappId%3DDev15IDEF1%26l%3DEN-US%26k%3Dk(LNK2005)%26rd%3Dtrue&view=vs-2019
{
	auto start = std::chrono::steady_clock::now();

	// Extra options:
	IntOption    verb("MAIN", "verb", "Verbosity level (0=silent, 1=some, 2=more).", 1, IntRange(0, 2));
	BoolOption   pre("MAIN", "pre", "Completely turn on/off any preprocessing.", true);
	StringOption dimacs("MAIN", "dimacs", "If given, stop after preprocessing and write the result to this file.");
	IntOption    cpu_lim("MAIN", "cpu-lim", "Limit on CPU time allowed in seconds.\n", INT32_MAX, IntRange(0, INT32_MAX));
	IntOption    mem_lim("MAIN", "mem-lim", "Limit on memory usage in megabytes.\n", INT32_MAX, IntRange(0, INT32_MAX));

	SimpSolver  S;
	double initial_time = cpuTime();

	if (!pre) S.eliminate(true);

	S.verbosity = verb;

	solver = &S;
	gzFile in = NULL;
	in = gzopen(input_file.c_str(), "rb"); //in = gzopen("input.txt", "rb");

	if (in == NULL)
		printf("ERROR! Could not open file: %s\n", input_file.c_str()), exit(1);

	parse_DIMACS(in, S);
	gzclose(in);
	
	S.eliminate(true);
	vec<Lit> dummy;
	lbool ret = S.solveLimited(dummy);   //calling the solver
	auto elapsed = std::chrono::steady_clock::now() - start;
	
	if (ret == l_True) {
		for (int i = 0; i < S.nVars(); i++)
			if (S.model[i] != l_Undef)
			{
				output_satisfiable_solution.satisfiable_string += (i == 0) ? "" : " ";
				output_satisfiable_solution.satisfiable_string += (S.model[i] == l_True) ? "" : "-";
				output_satisfiable_solution.satisfiable_string += to_string(i + 1);
			}
	}

	//set the cpu, conflicts measurements to be used later in get_avg(), get_max()
	output_satisfiable_solution.execution_time = std::chrono::duration<double> (elapsed).count(); //the units is (sec).
	output_satisfiable_solution.n_conflicts = S.conflicts;
}

inline void split_selection_clause_into_vectorOfClauses(const string& selection_clause, vector<_clause>& output_vector)
{
	//The implemenation of this method is different from the one in "generator.cpp", where there the (state) was always (true) for NW_struct1 or SIB_based networks
	//However now we can take an input from either an (input file) or from the (Generator) because of that we need to take SCB state into the considerations.

	size_t n = std::count(selection_clause.begin(), selection_clause.end(), '^');
	output_vector.reserve(n + 1); //A^B^C --> 2(^), 3(clauses).

	istringstream clause(selection_clause);
	string token;
	unsigned int itr;

	string id;
	string state_str_value;
	unsigned int state;

	while (getline(clause, token, '^'))
	{
		//first we need to trim any white space
		token = trim(token);

		itr = 0;//reset variables for the next time
		id = "";
		state_str_value = "";
		state = true;

		if (token[itr] == '!')
		{
			state = false;
			itr++; //to ignore (!) char while generating the (id)
		}

		while (token[itr] != '[' && token[itr] != '\0')
			id += token[itr++];

		if (token[itr] == '[')
		{
			while (token[++itr] != ']')
				state_str_value += token[itr];

			state = std::stoi(state_str_value, nullptr, 2);
		}

		output_vector.emplace_back(id, state);
	}
}