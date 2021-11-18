#ifndef SAT
#define SAT

#ifdef _MSC_VER				
#pragma once
#endif  // _MSC_VER

#include "structs.h"

//Global variables linkage externally
extern unsigned int max_no_TDRS;


class SAT_vertex
{
	string id;
	string selection_clause;
	string address_control_bit;
	unsigned int length;
	vector <string> predecessors; //we need both predecessor and successor pointers for SAT to check (SP_SS, SP_MS, MP_SS, MP_MS), (S,M,P,S): (single, multiple, predecesssor, successor) 
	vector <string> successors; //<unsigned int> these vector carry the Indices of successor and predeccor vertices; The trouble with using vector<vertex*> is that, whenever the vector goes out of scope unexpectedly(like when an exception is thrown), the vector cleans up after yourself, but this will only free the memory it manages for holding the pointer, not the memory you allocated for what the pointers are referring to.(https://stackoverflow.com/questions/1361139/how-to-avoid-memory-leaks-when-using-a-vector-of-pointers-to-dynamically-allocat/1361227)

public:
	//static variables: to be "initialized" only "once" in the scope of (all) class's objects.
	static string path;
	static unsigned int initial_configuration; 
	static bool Active_ReadWrite_access;  //true for Active, false for Read/Write
	static bool optimal_solution;   //false for First_Solution, true for Optimal_Solution
	static bool retarget_all_TDRs;
	static unsigned int no_CSUs;

	SAT_vertex(); //this constructor is used to Re-Build NW_graph from 'NW_graph.txt' file and Re-Build NW_clauses from 'NW_clauses.txt' file
	~SAT_vertex();

	SAT_vertex(const string &id, const string& selection_clause, const string &address_control_bit, unsigned int length, const string &predecessor, const string &successor)
		: id(id), selection_clause(selection_clause), address_control_bit(address_control_bit), length(length)
	{
		split_selection_clause_into_vectorOfClauses(predecessor, predecessors);

		split_selection_clause_into_vectorOfClauses(successor, successors);
	}

	SAT_vertex(const SAT_vertex& x)
		: id(x.id), selection_clause(x.selection_clause), address_control_bit(x.address_control_bit), length(x.length), predecessors(x.predecessors), successors(x.successors)
	{
		printf("SAT_vertex copied!!\n");
	}

	void load_NW_graph();	//these two methods are different from (generate_NW_graph, generate_NW_clauses) where we here just re build NW_graph and NW_clauses from input files.
	void load_target_reg();  //used to set (target_reg) name 

	//methods associated with Structured_SAT model
	measurements apply_SAT_retargeting(); //I need to return output as copy (not return by reference) since we are going to reset all NW_vectors for successor TDR's retargeting, so I need to keep one copy safe in main!!
	void generate_NW_structural_SAT_model();
	void reserve_vectors_memory(); //Very Important method used to minimze the number of copied objects and to adjust the capacity of used vectors for better performance
	void reset_system();
	void clear_vectors();
	void first_solution_model();
	void first_incremental_solution_model();
	void optimal_solution_model();
	void derive_SAT_predicates();
	void derive_incremental_SAT_predicates();
	void Initial_configuration_predicates(); //same method used with SCT_to_SAT model, and with structural_SAT model
	void CAM_read_predicates(unsigned int fromTF, unsigned int toTF); //CSU-Accurate RSN Model for reading requests
	void CAM_write_predicates(unsigned int fromTF, unsigned int toTF); //CSU-Accurate RSN Model for writing requests
	void CAM_predicates(unsigned int fromTF, unsigned int toTF); //"Generic" for write AND read requests.
	void State_transtion_predicates(unsigned int fromTF, unsigned int toTF); //TF:time frame
	void valid_scan_configuration_predicates(unsigned int timeFrame);
	void Active_ReadWrite_predicates();

	void convert_predicates_to_CNF();
	void convert_predicates_to_CNF_withIDs();
	bool is_SAT_instance_satisfiable();
	void generate_output_retargeting_vector();
	
	bool get_SelectControlInput(const string& id);
	const string& get_MUX_selectLines(const string& id);
	unsigned int get_length(const string& id);
	unsigned int get_SATvariable_no(const string& id, unsigned int timeFrame, unsigned int type);
	void map_SATAssignmentSolution_to_SATvariables();
	void set_SATvariable_assignment(unsigned int SAT_no, bool SAT_value);
	unsigned int get_SATvariable_assignment(const string& id, unsigned int timeFrame, unsigned int type);
	bool is_SCB(const string& id);
	void split_selection_clause_into_vectorOfClauses(const string& group_of_nodes, vector<string>& output_vector);
	void compute_no_clockCycles();
	void update_SAT_problem(const string& input_file);
	string get_negated_string(const string& input);

	void print_file(_SAT_Type option, const string& output_file, const string& file_opening_option);
	void print_vectors_size_capacity_comparison();
	void print_NWstatistics(bool target_statistics, unsigned int index = 0); //true: for "target_reg" statistics, false: for "whole NW" statistics.
	double get_avg(char x); //A->access time, C->CSU cycles, E->execution time, T->Traced nodes
	double get_max(char x);
};


#endif //SAT