#include "SAT.h"

//static variables (private variables to the scope of this file)
static size_t Expected_no_predicates, Expected_no_SATvariables, Expected_no_stateElements;
static vector<unsigned int> search_range; //this variable is used to speed up the search in (NW_SAT_variables) vector, where we only search in a specific range of SAT_variables which occur in the specific time frame. Index of this vector represents the timeFrame number; i.e. search_range[1]: means the search range associated with timeFrame(1)
static unsigned int no_timeFrames = 0; //this variable holds the "current", used number of time frames.
static unsigned int SATvariable_no;

static vector<SAT_vertex> NW_graph;
static vector<string> NW_stateElements; //NW_CSU_registers --> NW_SCBs. No need for NW_selectElements in Structured_SAT_model where all NW_graph elements have "select" variables
static vector<_SAT_predicate> NW_SAT_predicates;
static vector<string> NW_SAT_clauses;
static vector<_SAT_variable> NW_SAT_variables; //used to hold the boolean satisfiable values associated to each SAT_variable, which we get from the SAT solver
static vector<vector<_clause>> SAT_output;  //Two dimensional vector where each time frame has its ASP elements. used to hold the retargeting output vectors, by applying the boolean satisfiable values that we have got by the SAT_solver of each node in the network in each TF to get the Active Scan Path.
static vector<NWElement_statistics> NW_TDRs;

SAT_vertex::SAT_vertex()
{
	load_NW_graph(); //have to be called after setting the target_reg
	reserve_vectors_memory();
}

SAT_vertex::~SAT_vertex()
{
	vector<string>().swap(predecessors);
	vector<string>().swap(successors);
}

void SAT_vertex::reserve_vectors_memory()
{
	//initialize (SATvariable_no) 
	SATvariable_no = 1;

	//Following calculations are just based on finding a relation between numbers and figure out how we could put it in a mathematical equation. These expectations "are not exact" and are not optimum, so this specific prediction section for (Expected_no_predicates_forSCT, Expected_no_predicates_forSAT, Expected_no_SAT_variables) could be better predicted in the future.
	Expected_no_predicates = (NW_graph.size() * 5)*(no_CSUs + 1);	//(Expected_no_nodes / 2): represent NW_graph's size. (*4): assuming that each node in NW_graph generating (4) predicates on average, two for valid_scan_configuration and two for stat_tranition. (heirarchy_level+1): I need to acount the mux number of time frames which happen with writing requests since it needs one more CSU to update target_register with pdl's value. 
	Expected_no_SATvariables = (NW_graph.size() * 2)*(no_CSUs + 1) + 1; //(+1) at the end is only based on experiments and mulitple testing and not based on anything else!
	Expected_no_stateElements = NW_graph.size() / 2; //Most probably this is a good rnd choice; because AUX nodes in the NW_graph will compromize the mis-guessing.

	NW_SAT_predicates.reserve(Expected_no_predicates); //since (Expected_no_predicates) was calculated based on the SCT_to_SAT model. However, we want to reuse same calculations but through the structural_SAT model.
	NW_SAT_variables.reserve(Expected_no_SATvariables); //number of SAT variables almost equal to the number of predicates
	NW_stateElements.reserve(Expected_no_stateElements);

	// this vector is used as an index director to the SAT_variables associated to each timeFrame
	search_range.reserve(no_CSUs + 1); //no_timeFrames; since we need to set the search range for each timeFrame. (+1): for timeFrame (t0).
	SAT_output.reserve(no_CSUs + 1);   //(+1) to account also initial time frame (t0). Here we only reserve the outer vector capacity, and in the struct (_clause)'s constructor we reserve the internal vector capacity for each time frame.
}

void SAT_vertex::reset_system()
{
	std::vector<SAT_vertex>().swap(NW_graph);
	std::vector<_SAT_predicate>().swap(NW_SAT_predicates);
	std::vector<string>().swap(NW_SAT_clauses);
	std::vector<_SAT_variable>().swap(NW_SAT_variables);
	std::vector<string>().swap(NW_stateElements);
	std::vector<unsigned int>().swap(search_range);
	std::vector<vector<_clause>>().swap(SAT_output);
	vector<NWElement_statistics>().swap(NW_TDRs);
}

void SAT_vertex::clear_vectors()
{
	//initialize (SATvariable_no) 
	SATvariable_no = 1;

	NW_SAT_predicates.clear();
	NW_SAT_clauses.clear();
	NW_SAT_variables.clear();
	search_range.clear();
	SAT_output.clear();
}

void SAT_vertex::load_NW_graph()
{
	string input_file = path + "NW_graph.txt";

	std::ifstream data_file(input_file.c_str());
	string line;
	if (!data_file)
		printf("Cannot open the File : %s\n", input_file.c_str());

	else
	{
		unsigned int itr = 0, length = 0;
		string id, selection_clause, address_control_bit, predecessors, successors, len;
		bool isStateElement;

		//First line holds NW_graph size, we need to reserve capacity for NW_graph vector and push elements to it
		getline(data_file, line);
		NW_graph.reserve(stoi(line));

		while (getline(data_file, line))
		{
			itr = 0;
			id = "";
			selection_clause = "";
			address_control_bit = "";
			len = "";
			predecessors = "";
			successors = "";

			//{ "MUX[I1]-M2_1/34", "SR-M2_2/31^SR-M2_2/21", "SR-M2_2/31", 1, { SR-M2_2/31,  SR-M2_2/21}, { SR-M2_2/17 } }
			while (line[itr] != '"')
				itr++; //Do nothing! just increment the counter

			while (line[++itr] != '"')
				id += line[itr];

			while (line[++itr] != '"')
				; //Do nothing! just increment the counter

			while (line[++itr] != '"')
				selection_clause += line[itr];

			while (line[++itr] != '"')
				; //Do nothing! just increment the counter

			while (line[++itr] != '"')
				address_control_bit += line[itr];

			while (!isdigit(line[itr]))
				itr++; //Do nothing! just increment the counter

			while (line[itr] != ' ')
				len += line[itr++];
			length = stoi(len);

			while (line[itr] != '{')
				itr++; //Do nothing! just increment the counter

			while (line[++itr] != '}') //to count all predecessors; because I may have multiple.
				predecessors += line[itr];

			while (line[itr] != '{')
				itr++; //Do nothing! just increment the counter

			while (line[++itr] != '}') //to count all predecessors; because I may have multiple.
				successors += line[itr];

			//call initial constructor 
			NW_graph.emplace_back(id, selection_clause, address_control_bit, length, predecessors, successors);

			//this section to collect NW_stateElements: CSU_registers(SCBs).
			if (is_SCB(id))
				NW_stateElements.emplace_back(id);
		}
	}
}

void SAT_vertex::load_target_reg()
{
	//set (target_reg) name from "pdl" file
	//"In Future" I need to loop onto "vector<string>NW_TDRs", in order to generate the final report.
	string input_file = path + "NW_smv.pdl";
	std::ifstream data_file(input_file.c_str());
	string line, target_reg = "";
	if (data_file)
	{
		unsigned int itr = 0;

		//it is only one line there.
		getline(data_file, line);
		while (line[itr] != ' ')
			itr++;

		while (line[++itr] != ' ')
			target_reg += line[itr];

		NW_TDRs.emplace_back(target_reg);
	}
}

measurements SAT_vertex::apply_SAT_retargeting()
{
	if (!retarget_all_TDRs)
	{
		load_target_reg(); //from the (pdl) file.
		generate_NW_structural_SAT_model();
		print_NWstatistics(true); //means print NW_statistics for this "SPECIFIC" TDR.
	}
	else
	{
		NW_TDRs.reserve(NW_graph.size() - Expected_no_stateElements);
		for (size_t i = 0, e = NW_graph.size(); i < e; i++)
		{
			if (!is_SCB(NW_graph[i].id) && (NW_graph[i].id.find("AUX") == std::string::npos) && (NW_graph[i].id != "TDI") && (NW_graph[i].id != "TDO"))  //if the node is not belonging to either(scan registers) nor (Auxiliary nodes) nor (primary nodes), then it should be a shift_register or a TDR. 
			{
				NW_TDRs.emplace_back(NW_graph[i].id);
				generate_NW_structural_SAT_model(); //Here the NW_SAT_prediactes will be generated only once (through the first calling) and reUsed with each new target_reg, by changing only the Read/Write predicates.
				clear_vectors(); //reset the system for the next TDR retargeting 
			}
		}
		print_NWstatistics(false); //means print NW_statistics for the whole network for "ALL" Network_TDRS.
	}

	measurements execution_time(get_avg('E'), get_avg('C'), get_avg('A')); //this is the average of all network's TDRs retargeting times. The average calculated in the main() file, is the average of re-applying the retargeting process on the same network and under the same conditions for number of times (setted by the "no_readings" parameter).
	print_vectors_size_capacity_comparison(); ////Finally I need to 'update' (NW_vectors_sizes) with NW SAT vectors statistics
	reset_system();
	return execution_time;
}

void SAT_vertex::generate_NW_structural_SAT_model()
{
	//0- generate NW_scan_graph (or rebuild it from 'NW_graph' file)
	//1-push Initial_configurations_predicates (LHS)-state always driven from NW_state/initial configurations, while (RHS)-Active state would be driven from SCT-Active states tree 
	//2-for each timeFrame:
		//* push valid_scan_configuration_predicates	--> using (NW_graph) traversal
		//* push State_transtion_predicates				--> using (NW_clauses) associated with state elements
	//3-push read_write_target_configurations_predicates
	//4-Convert predicated into CNF clauses
	//5-Print the CNF clauses in a "DIMACS CNF" format
	//6-Enter the SAT variables into the SAT solver (MiniSAT)
	//7-Link between the solution/SAT assignment and each stateElement in the network according to the "SAT_variable_no.", by updating the value of "SAT_assignment" field
	//8-Generate the retargeting vector each time frame, until target register become accessible.
	////////////////////////////////////////////////////////////////

	if (!optimal_solution)
		first_incremental_solution_model();
	else 
		optimal_solution_model();

	if (NW_TDRs.back().solver_returns.size() == 0) //this condition is crucial because the SAT_problem may not have solution at all *using* the assigned number of CSUs
		printf("The Retargeting of (%s) is UNSATISFIABLE using (%d) CSUs\n", NW_TDRs.back().reg_id.c_str(), no_timeFrames);
}

void SAT_vertex::first_solution_model()
{
	derive_SAT_predicates(); //here we unroll the SAT Solver for only "one" time using the pre-defined number of CSUs.
	convert_predicates_to_CNF();
	//convert_predicates_to_CNF_withIDs(); //this method is only used for Eye's check

	if (is_SAT_instance_satisfiable()) //this condition is crucial because the SAT_problem may not have solution at all *using* the assigned number of CSUs
		printf("The Retargeting of (%s) is SATISFIABLE using (%d) CSUs\n", NW_TDRs.back().reg_id.c_str(), no_CSUs);
}

void SAT_vertex::first_incremental_solution_model()
{
	derive_incremental_SAT_predicates(); //here we construct an initial SAT_instance for the (TF=0) to be used in the "first unrollment" of the SAT_Solver inside the following (while loop).
	convert_predicates_to_CNF();

	while (!is_SAT_instance_satisfiable())
	{
		no_timeFrames++;
		derive_incremental_SAT_predicates(); //here we unroll the SAT Solver for a "number" of times until a solution is found. Iinitially (NW_TDRs.back().no_timeFrames = 0).
		convert_predicates_to_CNF();
	}

	no_CSUs = no_timeFrames;
	printf("The Retargeting of (%s) is SATISFIABLE using (%d) CSUs\n", NW_TDRs.back().reg_id.c_str(), no_CSUs);
}

void SAT_vertex::optimal_solution_model()
{
	unsigned int index_of_optimal_cost;	//which reflect the min number of Cycles needed for the optimal retargeting.
	NW_TDRs.back().solver_returns.reserve((no_CSUs + 1) * 5);        //(*5): this reservation is only a rnd value we pick without any scientific reason. so we are assuming that each time frame has an average of "5" different possible solutions. We are considering each TF; because when we enter that (#CSUs = 3) to the SAT solver, then it will look for solutions in (TF=0, TF=1, TF=2, TF=3) that's why we need to take all previous TFs into considerations while reserving the vector capacity.

	while (no_timeFrames <= no_CSUs)
	{
		derive_incremental_SAT_predicates(); //here we input the (UB_CSUs + SCT[SD+TD+LPC]).
		convert_predicates_to_CNF();

		//In optimal retargeting we apply multiple calls to the SAT_solver using (is_SAT_instance_satisfiable()) to search for all possible solutions in the search space using the assigned no_timeFrames until the whole space is examined and traversed and no other solutions could possibly exist.
		while (is_SAT_instance_satisfiable()) //This condition means it is not (UNSATISFIABLE) and the SAT_solver still finding other possible solutions.
			update_SAT_problem(path + "NW_structural_SAT.txt");	//update SAT_problem: append the "NEGATION" of the found solution to the SAT_problem to look for other solutions, until the solver returns (UNSATISFIABLE) or (empty) satisfiable_string inidicating that there is no other "different" solutions with this upper_bound number of CSUs.

		no_timeFrames++;
	}

	if (NW_TDRs.back().solver_returns.size() > 0) //this condition is crucial because the SAT_problem may not have solution at all using *all* the assigned number of CSUs.
	{
		index_of_optimal_cost = 0; //like min = x[0]; here we only set min value to the first index in the vector and compare others to it.
		for (size_t i = 1, e = NW_TDRs.back().solver_returns.size(); i < e; i++)
		{
			if (NW_TDRs.back().solver_returns[i].AccessTime < NW_TDRs.back().solver_returns[index_of_optimal_cost].AccessTime)
				index_of_optimal_cost = i;
		}
		printf("\n***Min number of clock cycles for the retargeting of (%s), using (%d) CSUs = %d***\n", NW_TDRs.back().reg_id.c_str(), NW_TDRs.back().solver_returns[index_of_optimal_cost].no_CSUs, NW_TDRs.back().solver_returns[index_of_optimal_cost].AccessTime);
	}
}

void SAT_vertex::derive_SAT_predicates()
{
	if (NW_SAT_predicates.size() == 0) //if the SAT_problem was not created before
	{
		//1- Add initial configuration clauses
		Initial_configuration_predicates();

		//2- Add NW_validity and stateElements_transition_predicates in each time frame.
		for (unsigned int TF = 0; TF < no_CSUs; TF++)
			CAM_predicates(TF, TF + 1); //this is the a general model for both (Read) and (Write) requets.

		/*
		//Or we could call a specific CAM_model based on the type of request (Read or Write)?
		void(SAT_vertex::*fcnPtr)(unsigned int, unsigned int);		// fcnPtr is a pointer to a function that takes two arguments and returns Nothing.
		fcnPtr = &SAT_vertex::CAM_write_predicates; //this is the default
		if (!write_read_access)
			fcnPtr = &SAT_vertex::CAM_read_predicates;

		for (unsigned int TF = 0; TF < no_timeFrames; TF++)
			(this->*fcnPtr)(TF, TF + 1); //To invoke the method, use the [this->*] operator or [*this.*]
		*/

		//3- Add target configuration predicates, based on if it was read/write request.
		Active_ReadWrite_predicates();
		NW_TDRs.back().n_SAT_variables = NW_SAT_variables.size();
	}
	else //in case of (test_all_TDRs), different TDRs have "same" NW_SAT_predicates with only change in (write_read_predicates()) to be compatable with the "new" target_reg.
	{
		NW_SAT_predicates.erase(NW_SAT_predicates.end() - 1); //remove the predicate associated with the read/write of the old (target_reg) and replace it with the new one!!
		Active_ReadWrite_predicates(); //regenerate it for the "new" target_reg
		NW_TDRs.back().n_SAT_variables = NW_SAT_variables.size(); //set the number of (SAT_variables) to the "new" target_reg.
	}	
}

void SAT_vertex::derive_incremental_SAT_predicates()
{
	if (no_timeFrames == 0) //if the SAT_problem was not created before
	{
		//1- Add initial configuration clauses
		Initial_configuration_predicates();

		//2- Add target configuration predicates, based on if it was read/write request.
		Active_ReadWrite_predicates();
		NW_TDRs.back().n_SAT_variables = NW_SAT_variables.size();
	}
	else //here we use the (incremental_SAT) in successor time frames.
	{
		//1- Remove the predicate associated with the read/write of the old (time frame) and integrate with them the predicates associated with the new added time frame!!
		NW_SAT_predicates.erase(NW_SAT_predicates.end() - 1);
		
		//2- Add NW_validity and stateElements_transition_predicates for the new time frame.
		CAM_predicates(no_timeFrames - 1, no_timeFrames); //this is the a general model for both (Read) and (Write) requets.
		/*
		//Or we could call a specific CAM_model based on the type of request (Read or Write)?
		void(SAT_vertex::*fcnPtr)(unsigned int, unsigned int);		// fcnPtr is a pointer to a function that takes two arguments and returns Nothing.
		fcnPtr = &SAT_vertex::CAM_write_predicates; //this is the default
		if (!write_read_access)
			fcnPtr = &SAT_vertex::CAM_read_predicates;

		(this->*fcnPtr)(no_timeFrames - 1, no_timeFrames); //To invoke the method, use the [this->*] operator or [*this.*]
		*/

		//3- Regenerate it for the "added" time frame
		Active_ReadWrite_predicates();
		
		NW_TDRs.back().n_SAT_variables = NW_SAT_variables.size(); //set the number of (SAT_variables) to the "new" target_reg.
	}
}

void SAT_vertex::Initial_configuration_predicates()
{
	bool initial_select; //initial_sel can be generated also while generating the netwoek itself using NW_generator, where we can process scan segment's selection clause and compare it with NW initial congiuration and then assign to each element in the network its initial_select; but this way could be better in case we want to test external NW (not the one created by the generator) or if we want to try different NW_configurations. So, this way gives more flexibility.
	search_range.emplace_back(NW_SAT_variables.size());  //this is the NW_SAT_variables's search_range for time frame(t0). it means the search_range of SAT_variables associated with timeFrame(0) starts from index[0], where initially: (NW_SAT_variables.size()=0).

	//1- Insert the initial state of (Network "Scan Registers" or "address" state of each multiplexer in the network)
	for (size_t i = 0, e = NW_stateElements.size(); i < e; i++)
	{
		//insert initial "state_clause" of NW scan segments: this holds state(SCB, TF=0). It is needed in state_transition_predicates where I need to know the initial_state to go to the next state or next configuration: state(SCB,t0) XOR state(SCB, t1) --> select(SCB,t0)
		NW_SAT_predicates.emplace_back(NW_stateElements[i], 0, 1, initial_configuration);
		NW_SAT_variables.emplace_back(NW_stateElements[i], 0, 1, SATvariable_no++);
	}

	//2- Insert the initial_select of Network Scan Segments
	for (size_t i = 0, e = NW_graph.size(); i < e; i++)
	{
		//insert initial "select_clause": this holds select(SCB, TF=0). It is needed in state_transition_predicates where we only update scan segment state if it is Active and part of the ASP: [select=TRUE] in state(SCB,t0) XOR state(SCB, t1) --> select(SCB,t0). also we need the select() signal in generating the ASP of each time frame including (t0).
		initial_select = get_SelectControlInput(NW_graph[i].id);
		NW_SAT_predicates.emplace_back(NW_graph[i].id, 0, 2, initial_select);
		NW_SAT_variables.emplace_back(NW_graph[i].id, 0, 2, SATvariable_no++);
	}
}

void SAT_vertex::CAM_read_predicates(unsigned int fromTF, unsigned int toTF) //CSU-Accurate RSN Model
{
	/*
	sequence in "Read" requests:
	First, if target_reg is not Active in timeFrame(0), then I need to change NW_state to another state and then check if target_reg is now Active or not?
		   So, we need first to take the network to another possible state using "state_transition(0, 1)".
	Secondly, get the "new" ASP associated with the new network scan configuration (TF+1).
	Finally, we use "read_predicates" to check if target_reg is now Active in the new network state or not.

	Note:
	-Min number of time frames for any read request is (0), and that's happen the target_reg is already belongs to the ASP (selection_clause="TRUE") and I can read its value directly.
	*/

	//Here we insert new record in the "search_range" vector associated with the index of all 'SAT_variables' that exist in the next time frame "toTF:(t+1)"
	search_range.emplace_back(NW_SAT_variables.size()); //this is the search range associated with timeFrame/index (t+1) not (t).

	//1- Transition Relation of the CSU_Accurate Model(CAM): (fromTF, toTF)
	State_transtion_predicates(fromTF, toTF);

	//2- Valid Scan Configuration: (toTF)
	valid_scan_configuration_predicates(toTF);
}

void SAT_vertex::CAM_write_predicates(unsigned int fromTF, unsigned int toTF) //CSU-Accurate RSN Model
{
	/*
	sequence in "Write" requests:
	First, get ASP for the current timeFrame using "valid_scan_configuration_predicates".
	Second, apply "state_transition" from timeFrame to another for each scan segment element (SUC) and for the target_register
	Finally, check if the value in pdl file has been shifted correctly to the target_reg using "write_predicates".

	Notes:
	1- for (TF=0) we can apply "state_transition" predicates directly, where initial_select or select(TF=0) predicates were already included through "initial_configuration" predicates.
	2- Min number of time frames for any write request is (1), and that is when the target_reg is already in ASP (selection_clause="TRUE") and we need only one extra time frame to write on Active register.
	*/

	if (fromTF != 0) //for (TF>0) I need to detect first the ASP using "valid_scan_configuration_predicates", so that we could be able to apply "state_transition".
	{
		//1- Valid Scan Configuration: (fromTF)
		valid_scan_configuration_predicates(fromTF);

		//Here we set the SAT_variables' search range for time frame "toTF:(t+1)"
		search_range.emplace_back(NW_SAT_variables.size()); //this is the search range associated with timeFrame/index (t+1) not (t).

		//2- Transition Relation of the CSU_Accurate Model(CAM): (fromTF, toTF)
		State_transtion_predicates(fromTF, toTF);
	}
	else
	{
		search_range.emplace_back(NW_SAT_variables.size()); //this is the search range associated with timeFrame/index (t+1) not (t).
		State_transtion_predicates(fromTF, toTF);
	}
}

void SAT_vertex::CAM_predicates(unsigned int fromTF, unsigned int toTF) //CSU-Accurate RSN Model
{
	/*
	sequence:
	First, apply NW_transition to a "new" configuration.
	Second, get the "new" ASP associated with the new network scan configuration (TF+1).
	Finally, use "read_write_predicates" to check if the target_reg is now Active/Updated with the (SI) bits as requested or not.
	*/

	//Here we insert new record in the "search_range" vector associated with the index of all 'SAT_variables' that exist in the next time frame "toTF:(t+1)"
	search_range.emplace_back(NW_SAT_variables.size()); //this is the search range associated with timeFrame/index (t+1) not (t).

	//1- Transition Relation of the CSU_Accurate Model(CAM): (fromTF, toTF)
	State_transtion_predicates(fromTF, toTF);

	//2- Valid Scan Configuration: (toTF)
	valid_scan_configuration_predicates(toTF);
}

void SAT_vertex::valid_scan_configuration_predicates(unsigned int timeFrame)
{
	///////////////////////////////////////////////////////////////////////////////////////////////
	//for scan segment could have "four" possibilities:
	//1- SP_SS, like (In, Out, SC, AUX) vertices
	//2- SP_MS, like (Br) vertices. in cas of "fan out".
	//3- MP_SS, like (SR) vertices [SR then MUX_I1]. in case of multiplexers.
	//4- MP_MS, like (SR) vertices [SR then Br]. in case of a multiplexer constitutes a fanout stem with "no" intermediate scan segment.
	///////////////////////////////////////////////////////////////////////////////////////////////

	for (size_t index = 0, e1 = NW_graph.size(); index < e1; index++)
	{
		//I need to generate a SAT_number for this (select) variables; note that this NW_SAT_variables with [type=2] for [sel()] are differnet from the ones generated in (State_transtion_predicates) method with [type=1] for [state()].
		NW_SAT_variables.emplace_back(NW_graph[index].id, timeFrame, 2, SATvariable_no++);

		//1- This section for: sel(v) --> sel(p) OR sel(v) --> ||sel(p), if I have many predecessors.
		NW_SAT_predicates.emplace_back(NW_graph[index].predecessors.size() + 1);  //(+1) for the node itself (v)
		NW_SAT_predicates.back().SAT_literals.emplace_back(NW_graph[index].id, timeFrame, 2, (NW_graph[index].predecessors.size() != 0) ? 0 : 1); //(0 : 1); because sel(v) --> sel(p) means (!sel(v) OR sel(p)), however, in case of no predecessor nodes like (TDI) vertex, we need to add this predicate (sel(TDI)) which means it is always should be "TRUE".
		for (size_t n = 0, e = NW_graph[index].predecessors.size(); n < e; n++)
			NW_SAT_predicates.back().SAT_literals.emplace_back(NW_graph[index].predecessors[n], timeFrame, 2, 1);

		//2- This section for: sel(v) --> sel(s) OR sel(v) --> ||sel(s), if I have many successors.
		NW_SAT_predicates.emplace_back(NW_graph[index].successors.size() + 1);
		NW_SAT_predicates.back().SAT_literals.emplace_back(NW_graph[index].id, timeFrame, 2, (NW_graph[index].successors.size() != 0) ? 0 : 1); //(0 : 1); because sel(v) --> sel(s) means (!sel(v) OR sel(s)), however, in case of no successor nodes like (TDO) vertex, we need to add this predicate (sel(TDO)) which means it is always should be "TRUE".
		for (size_t n = 0, e = NW_graph[index].successors.size(); n < e; n++)
			NW_SAT_predicates.back().SAT_literals.emplace_back(NW_graph[index].successors[n], timeFrame, 2, 1);

		//3- This section to assure valid scan configuration which requires that at most one predecessor of (v) is active. The predicate assures that in case of a multiplexed scan path the active scan path is correctly routed.
		//i.e. sel(p)-->address=addr(p), node's predecessor should be correctly selected by the (address) signal of the multiplexer.
		if (NW_graph[index].predecessors.size() > 1)
		{
			if (NW_graph[index].predecessors.size() == 2)
			{
				for (size_t n = 0, e = NW_graph[index].predecessors.size(); n < e; n++)
				{
					NW_SAT_predicates.emplace_back(2);
					NW_SAT_predicates.back().SAT_literals.emplace_back(NW_graph[index].predecessors[n], timeFrame, 2, 0); //0 because (sel(p)-->address=addr(p)) means (!sel(p) OR address=addr(p))
					NW_SAT_predicates.back().SAT_literals.emplace_back(get_MUX_selectLines(NW_graph[index].predecessors[n]), timeFrame, 1, n); //true: because MUX's address_control_bit is controlled by some SCB's state varibale (state(SR4)). (n) this not perfect and not a totally correct value to be used in method's implementation, but I'm assuming that the MUX inputs are inserted as the same way that (n) would change through the loop, i.e. first input(n=0) would be selected when (address control bit = 0), second input (n=1) would be selected when (address control bit = 1), so, here MUX_selected_input = n_value, but this should not be generalized and need to be more sophisticated (developed to a high degree of complexity) :)	
				}
			}
			else	//if(NW_graph[index].predecessors.size() > 2) then this is "NOT" a (2*1) MUX and it will have more than one selection lines.
			{
				vector<string> selectionLines;
				split_selection_clause_into_vectorOfClauses(get_MUX_selectLines(NW_graph[index].predecessors[0]), selectionLines); //(NW_graph[index].predecessors[0]) we can choose any of the predecessors they all have the same selectionLines because they all are the inputs for the "same" MUX.

				int binary_value, num;

				for (size_t n = 0, e = NW_graph[index].predecessors.size(); n < e; n++)
				{
					num = n;
					for (size_t s = 0, e = selectionLines.size(); s < e; s++)
					{
						binary_value = num % 2;

						NW_SAT_predicates.emplace_back(2);
						NW_SAT_predicates.back().SAT_literals.emplace_back(NW_graph[index].predecessors[n], timeFrame, 2, 0);
						NW_SAT_predicates.back().SAT_literals.emplace_back(selectionLines[s], timeFrame, 1, binary_value);

						num /= 2;
					}
				}
			}
		}

		//4- This section to assure valid scan configuration which requires that at most one successor of (v) is active. This predicate assures that in case of fan-out the active scan path doesn't branch.
		//i.e. if I have 3 successors (A, B, C) then {sel(A)->!sel(B)^!sel(C), sel(B)->!sel(A)^!sel(C), sel(C)->!sel(A)^!sel(B)} OR we could say: (sel(A)->!sel(B)) ^ (sel(A)->!sel(C)) ^ ((sel(B)->!sel(C))
		if (NW_graph[index].successors.size() > 1)
		{
			for (size_t n = 0, e1 = NW_graph[index].successors.size() - 1; n < e1; n++)
			{
				for (size_t m = n + 1, e2 = NW_graph[index].successors.size(); m < e2; m++)
				{
					NW_SAT_predicates.emplace_back(2); //(sel(A)->!sel(B)) --> !sel(A) OR !sel(B)
					NW_SAT_predicates.back().SAT_literals.emplace_back(NW_graph[index].successors[n], timeFrame, 2, 0); //0 because !sel(A)
					NW_SAT_predicates.back().SAT_literals.emplace_back(NW_graph[index].successors[m], timeFrame, 2, 0); //0 bcz !sel(m) is negated; sel(A)-->!sel(B).
				}
			}
		}

	}
}

void SAT_vertex::State_transtion_predicates(unsigned int fromTF, unsigned int toTF)
{
	for (size_t index = 0, e1 = NW_stateElements.size(); index < e1; index++)
	{
		NW_SAT_variables.emplace_back(NW_stateElements[index], toTF, 1, SATvariable_no++);

		NW_SAT_predicates.emplace_back(3);
		NW_SAT_predicates.back().SAT_literals.emplace_back(NW_stateElements[index], fromTF, 1, 0);  //(!A OR B OR C) 
		NW_SAT_predicates.back().SAT_literals.emplace_back(NW_stateElements[index], toTF, 1, 1);
		NW_SAT_predicates.back().SAT_literals.emplace_back(NW_stateElements[index], fromTF, 2, 1);

		NW_SAT_predicates.emplace_back(3);
		NW_SAT_predicates.back().SAT_literals.emplace_back(NW_stateElements[index], fromTF, 1, 1);  //(A OR !B OR C) 
		NW_SAT_predicates.back().SAT_literals.emplace_back(NW_stateElements[index], toTF, 1, 0);
		NW_SAT_predicates.back().SAT_literals.emplace_back(NW_stateElements[index], fromTF, 2, 1);
	}
}

void SAT_vertex::Active_ReadWrite_predicates()
{
	//this section to insure that the target_reg was active through any time frame.
	unsigned int Active_TFs = 0; //refers to the number of time frames that should be active in case of write and read access requets.

	if (Active_ReadWrite_access) //For "Active" requests
		Active_TFs = no_timeFrames;  //in Active Access: Retargeting stops "once" the target_reg's structural dependencies becomes satisfied and therefore the target_reg would be Active during the following time frame.
	else if (no_timeFrames > 0)//For "Read/Write Access"
		Active_TFs = no_timeFrames - 1;	//in Read/Write Access: Retargeting stops "after" at least one cycle from putting the target_reg on the ASP, i.e. the target_reg should becomes Active before the final_CSU by at least by one time frame to satisfy the read or write requests through the *last* time frame, that's why we write (no_timeFrames - 1).

	NW_SAT_predicates.emplace_back(Active_TFs + 1); //(+1) to include also the timeFrame (t0)

	//for "Read" access we need to include checking if the target_reg become Active eventually at the "last" time frame or not; however, for "Write" access we need to check only if target_reg is Active at any "previously" time frame, where the last time frame is used in updating the target_reg with the required shift value.
	for (unsigned int t = 0; t <= Active_TFs; t++) //(<=) because for "Write" requests, I need the target_reg to be Active at "any" previous timeFrame, that's why we use the "Less_than" (<). However, for "Read" requests, I need the target_reg to be Active in any time frame "including" the "last" timeFrame, that's why we use the "Equality" (=). 
		NW_SAT_predicates.back().SAT_literals.emplace_back(NW_TDRs.back().reg_id, t, 2, 1); //"1" because I need the target_reg to be accessable to me(Selected or Active) through any time frame so that I can access it and capture/read its register value or update/write over it.
	/*
	if (!write_read_access) //for "Read" access we need to check if the target_reg become Active eventually at the "last" time frame or not.
		NW_SAT_predicates.back().SAT_literals.emplace_back(target_reg, no_timeFrames, false, 1);
	else		//this section is concerning with the "Write" access requests to insure if the value in the pdl file (iWrite ..) has been written into the target_reg or not.
		NW_SAT_predicates.emplace_back(target_reg, no_timeFrames, true, 1);  //Test case: for a write access request, check that "1" is written finally in the target_reg.
	*/
}

void SAT_vertex::convert_predicates_to_CNF()
{
	string CNF_clause, negation;
	
	//First we need to clear the old SAT problem in case of any and we replace it with the new one. (new SAT instance could represents the "same" retargeting/UBC problem but using "more" number of time frames, or it could represents "different" retargeting/UBC problem for another NW_TDR in the same network. That's why we need each time to clear/reset the old instance first.
	if (NW_SAT_clauses.size() == 0)
		NW_SAT_clauses.reserve(NW_SAT_predicates.size() + 1 + NW_TDRs.back().solver_returns.capacity()); //SAT_clauses vector has the same size as SAT_predicates vector; where the only difference between the two vectors is that in SAT_clauses vector we replace each SAT_literal with its corresponding SAT_no, also (+1) to account for the "p cnf " line, (+possibleRetargetings.capacity()) in case the user request the optimal solution, where we have to append to the CNF clauses all the found/possible solutions
	else
		NW_SAT_clauses.clear();

	CNF_clause = "p cnf " + to_string(SATvariable_no - 1) + " " + to_string(NW_SAT_predicates.size()); //(SATvariable_no - 1) because we use (++) --> SATvariable_no++. 
	NW_SAT_clauses.emplace_back(CNF_clause);

	for (size_t i = 0, e1 = NW_SAT_predicates.size(); i < e1; i++)
	{
		CNF_clause = "";
		for (size_t j = 0, e2 = NW_SAT_predicates[i].SAT_literals.size(); j < e2; j++)
		{
			negation = (NW_SAT_predicates[i].SAT_literals[j].state == 0) ? "-" : "";
			CNF_clause += negation + to_string(get_SATvariable_no(NW_SAT_predicates[i].SAT_literals[j].id, NW_SAT_predicates[i].SAT_literals[j].timeFrame, NW_SAT_predicates[i].SAT_literals[j].type)) + " ";

			if (j == e2 - 1)
				CNF_clause += "0";
		}

		NW_SAT_clauses.emplace_back(CNF_clause);
	}
	NW_TDRs.back().n_SAT_clauses = NW_SAT_clauses.size() - 1; //to exclude the first line (p CNF ..)
	
	//This is a *very important* step for (the Retargeting of Optimal solutions): where we need to exclude also all previously examined solutions from the search space as they were already considered before in our possible retargeting solutions; and this is by incuding their negated_satisfiable_string in our SAT_problem.
	if (optimal_solution && no_CSUs != -1) //(no_CSUs != -1) this is needed to NOT consider the (UBC) problems
	{
		for (unsigned int i = 0, e1 = NW_TDRs.size(); i < e1; i++)
		{
			for (unsigned int j = 0, e2 = NW_TDRs[i].solver_returns.size(); j < e2; j++)
				NW_SAT_clauses.emplace_back(get_negated_string(NW_TDRs[i].solver_returns[j].satisfiable_string));
		}

		//Next update the number of SAT clauses to include the previously examined retargeting solutions also, using the updated size value (NW_SAT_clauses.size()).
		if (NW_SAT_predicates.size() < NW_SAT_clauses.size() - 1) //means a satisfying_assignment solutions have beed added and we need to re-update the no_SAT_clauses. (NW_SAT_clauses.size() - 1): (-1) to unconsider the (p cnf ..) clause.
			NW_SAT_clauses[0] = "p cnf " + to_string(SATvariable_no - 1) + " " + to_string(NW_SAT_clauses.size() - 1);
	}

	print_file(SAT_clauses, path + "NW_structural_SAT.txt", "w"); //reWrite the CNF file with the new read/write clause.
}

void SAT_vertex::convert_predicates_to_CNF_withIDs()
{
	NW_SAT_clauses.clear(); //to clear the first CNF clauses created by the previous (convert_predicates_to_CNF) calling.

	string CNF_clause;
	CNF_clause = "\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\";
	NW_SAT_clauses.emplace_back(CNF_clause);
	CNF_clause = "p cnf " + to_string(SATvariable_no - 1) + " " + to_string(NW_SAT_predicates.size());
	NW_SAT_clauses.emplace_back(CNF_clause);

	for (size_t i = 0, e1 = NW_SAT_predicates.size(); i < e1; i++)
	{
		CNF_clause = "";
		for (size_t j = 0, e2 = NW_SAT_predicates[i].SAT_literals.size(); j < e2; j++)
		{
			CNF_clause += (NW_SAT_predicates[i].SAT_literals[j].state == 0) ? "-" : "";
			CNF_clause += NW_SAT_predicates[i].SAT_literals[j].type == 1 ? "state(" : "sel(";
			CNF_clause += NW_SAT_predicates[i].SAT_literals[j].id + ", " + to_string(NW_SAT_predicates[i].SAT_literals[j].timeFrame) + ", " + to_string(get_SATvariable_no(NW_SAT_predicates[i].SAT_literals[j].id, NW_SAT_predicates[i].SAT_literals[j].timeFrame, NW_SAT_predicates[i].SAT_literals[j].type)) + ") ";

			if (j == e2 - 1)
				CNF_clause += "0";

		}

		NW_SAT_clauses.emplace_back(CNF_clause);
	}

	// here we append "a" to the original SAT_clauses, the same SAT_clauses but writen in meaningful or understandable way!!
	print_file(SAT_clauses, path + "NW_structural_SAT.txt", "a");
}

bool SAT_vertex::get_SelectControlInput(const string& id)
{
	string token;
	unsigned int i, e, SCB_state;
	//reservation of (NW_clauses.back().clause.reserve) implemented in struct (selection_clause) constructor

	for (i = 0, e = NW_graph.size(); i < e; i++)
	{
		if (id == NW_graph[i].id)
			break;
	}

	if (NW_graph[i].selection_clause == "TRUE")
		return true;
	else
	{
		istringstream clause(NW_graph[i].selection_clause);
		while (getline(clause, token, '^'))
		{
			//register is Active or Selected if the state of "all" SCBs in its selection clause is equivalent to NW_current_state (initial_configuration)
			SCB_state = (token[0] == '!') ? 0 : 1;

			if (SCB_state != initial_configuration) //if only one not consisent, return false; because all SCBs in the selection clause are ANDed together, so any false will break the whole.
				return false;
		}
		return true;
	}
}

const string& SAT_vertex::get_MUX_selectLines(const string& id)
{
	for (size_t i = 0, e = NW_graph.size(); i < e; i++)
	{
		if (NW_graph[i].id == id)
			return NW_graph[i].address_control_bit;
	}
}

unsigned int SAT_vertex::get_length(const string& id)
{
	for (size_t i = 0, e = NW_graph.size(); i < e; i++)
	{
		if (NW_graph[i].id == id)
			return NW_graph[i].length;
	}
}

unsigned int SAT_vertex::get_SATvariable_no(const string& id, unsigned int timeFrame, unsigned int type)
{
	//For "Structured_SAT" key=(id, timeFrame, type); type is necessary because I could have SAT_variable for [state(SR3,t0)] and [select(SR3,t0)] both in the same timeFrame, so I need type flag to get the correct SAT_variable_no
	//EX:(SR3, t1, false) means Active/Select(SR3, t1)

	//To speed up searching in (NW_SAT_variables) we use 'search_range' variable to search on SATvariable_no within specific/limited range and not through the whole range
	unsigned int start, stop;
	start = search_range[timeFrame];
	stop = (timeFrame != no_timeFrames) ? search_range[timeFrame + 1] : NW_SAT_variables.size();

	for (unsigned int index = start; index < stop; index++)
	{
		if ((NW_SAT_variables[index].id == id) && (NW_SAT_variables[index].type == type))
			return NW_SAT_variables[index].SAT_no;
	}

	printf("SAT_variable doesn't exist !!\n");
	exit(0); //if SAT_variable doesn't exist
}

void SAT_vertex::set_SATvariable_assignment(unsigned int SAT_no, bool SAT_value)
{
	//first loop is used to set the SAT_variable to the correct group of SAT_variables which exist in the same time frame, to speed up the search and not to be through the whole NW_SAT_variables range.
	unsigned int start_index, stop_index;
	for (unsigned int TF = 0; TF <= no_timeFrames; TF++)
	{
		start_index = search_range[TF];
		stop_index = (TF != no_timeFrames) ? search_range[TF + 1] : NW_SAT_variables.size();

		if ((SAT_no >= start_index) && (SAT_no <= stop_index))
			break; //then this is the correct/limited range which we need to search in.
	}

	for (unsigned int index = start_index; index <= stop_index; index++) //only search betwean (start_index, stop_index)
	{
		if (NW_SAT_variables[index].SAT_no == SAT_no)
		{
			NW_SAT_variables[index].SAT_assignment = SAT_value;
			return;
		}
	}

	printf("SAT_variable doesn't exist !!\n");
	exit(0); //if SAT_variable doesn't exist
}

unsigned int SAT_vertex::get_SATvariable_assignment(const string& id, unsigned int timeFrame, unsigned int type)
{
	unsigned int start, stop;
	start = search_range[timeFrame];
	stop = (timeFrame != no_timeFrames) ? search_range[timeFrame + 1] : NW_SAT_variables.size();

	for (unsigned int index = start; index < stop; index++)
	{
		if ((NW_SAT_variables[index].id == id) && (NW_SAT_variables[index].type == type))
			return NW_SAT_variables[index].SAT_assignment;
	}

	printf("SAT_variable doesn't exist !!\n");
	exit(0); //"Means it doesn't exist; 
}

bool SAT_vertex::is_SCB(const string& id)
{
	if ((id.find("SR") != std::string::npos) || (id.find("SCB") != std::string::npos))
		return true;

	return false;
}

void SAT_vertex::split_selection_clause_into_vectorOfClauses(const string& group_of_nodes, vector<string>& output_vector)
{
	//The implemenation of this method is different from the one in "generator.cpp", where there the (state) was always (true) for NW_struct1 or SIB_based networks
	//However now we can take an input from either an (input file) or from the (Generator) because of that we need to take SCB state into the considerations.

	size_t n = std::count(group_of_nodes.begin(), group_of_nodes.end(), ',');
	output_vector.reserve(n + 1);

	istringstream nodes(group_of_nodes);
	string token;

	while (getline(nodes, token, ','))
	{
		token = trim(token); //used to trim white spaces if there
		output_vector.emplace_back(token);
	}
}

void SAT_vertex::compute_no_clockCycles()
{
	unsigned int no_clkCycles = 0;

	for (size_t i = 0, e1 = SAT_output.size(); i < e1; i++)
	{
		for (size_t j = 0, e2 = SAT_output[i].size(); j < e2; j++)
		{
			no_clkCycles += get_length(SAT_output[i][j].clause);
		}

		no_clkCycles += 2; //(+2) for the update and capture operations.
	}

	NW_TDRs.back().solver_returns.back().AccessTime = no_clkCycles;
}

void SAT_vertex::update_SAT_problem(const string& file_name)
{
	//This method is used to append only the "negation" of the (state registers) in the satisfiable_string to the SAT_problem but we need to reWrite the "NW_structural_SAT.txt" file because the number of SAT clauses has been updated and we need to reflect that in the first line of the CNF file be reWriting it.
	//First update the number of SAT clauses to include the (negated_staisfiable_str) clause also, using the updated size value (NW_SAT_clauses.size()).
	NW_SAT_clauses[0] = "p cnf " + to_string(SATvariable_no - 1) + " " + to_string(NW_SAT_clauses.size());
	
	//Second append the (negated_staisfiable_str) to the original SAT problem.
	NW_SAT_clauses.emplace_back(get_negated_string(NW_TDRs.back().solver_returns.back().satisfiable_string));
	
	//Third reWrite the SAT problem taking into consideration all found solution to let the SAT solver seek for other different solutions.
	print_file(SAT_clauses, path + "NW_structural_SAT.txt", "w");

	//Finally reset the (SAT_output) to be used in the next retargeting.
	SAT_output.clear();
}

string SAT_vertex::get_negated_string(const string& input)
{
	istringstream SAT_assignment(input);
	string token, SAT_variable, negated_staisfiable_str = "";
	unsigned int itr;
	bool is_negated;

	while (getline(SAT_assignment, token, ' '))
	{
		is_negated = false;
		itr = 0;
		SAT_variable = "";

		if (token[0] != '-')
			SAT_variable = token + " ";
		else
		{
			is_negated = true;
			itr++;// ignore the sign from the SAT_no
			while (token[itr] != '\0')
				SAT_variable += token[itr++];

			SAT_variable += " ";
		}

		negated_staisfiable_str += is_negated ? SAT_variable : "-" + SAT_variable; //invert the assignment value to exclude this assignment_solution from the next possible_retaregeting
	}
	negated_staisfiable_str += "0"; //where each CNF clause should end with "0".

	return negated_staisfiable_str;
}

bool SAT_vertex::is_SAT_instance_satisfiable()
{
	//0- adjust a place in the (solver_returns) vector to be "directly" used in setting SAT_solver output values.
	NW_TDRs.back().solver_returns.emplace_back();

	//1- run the SAT_solver on the updated (SAT_problem), updated with other found solutions in case of optimal_retargeting active choice.
	run_SAT_solver_withNoPrint(path + "NW_structural_SAT.txt", NW_TDRs.back().solver_returns.back());
	if (NW_TDRs.back().solver_returns.back().n_conflicts > 0)
		printf("\nSAT solver has conflicts = %d, while retargeting (%s)\n", NW_TDRs.back().solver_returns.back().n_conflicts, NW_TDRs.back().reg_id.c_str());

	if (NW_TDRs.back().solver_returns.back().satisfiable_string.length() != 0) //means the problem is "SATISFIABLE"
	{
		//2- assign the currently used number of time frames to the SAT solutionn we just got.
		NW_TDRs.back().solver_returns.back().no_CSUs = no_timeFrames;
		
		//3- set (SAT_assignment) values returned by the SAT solver for each SAT vertex in the network, this operation should be applied on each time frame.
		map_SATAssignmentSolution_to_SATvariables();

		//4- Generate Active Scan Path associated with each time frame.
		generate_output_retargeting_vector();

		//5- Compute the number of clock cycles for the Retargeting_Solution associated with the current satisfiable_string;
		compute_no_clockCycles();

		//6- Generate NW "retargeting" output vectors which should be entered to the TAP controller to read/write the value in the target_reg,
		print_file(SAT_retargeting_vectors, path + "NW_structural_SAT_retargeting_vectors.txt", "a"); //"a": to append all found solution in case of (Optimal_Solution) retargeting

		return true;
	}	
	else
	{
		//7- Remove the last UNSATISFIABLE Solution from (NW_TDRs.back().solver_returns) vector; because it has no (assignment_solution) using the assigned number of time frames.
		NW_TDRs.back().solver_returns.erase(NW_TDRs.back().solver_returns.end() - 1);
		return false;
	}
}

void SAT_vertex::map_SATAssignmentSolution_to_SATvariables() //extract SAT_assignment values from the "SATISFIABLE" string
{
	istringstream SAT_assignment(NW_TDRs.back().solver_returns.back().satisfiable_string);
	string token, SAT_variable;
	unsigned int itr;
	bool SAT_value;

	while (getline(SAT_assignment, token, ' '))
	{
		SAT_value = true;
		itr = 0;
		SAT_variable = "";

		if (token[0] != '-')
			SAT_variable = token;
		else
		{
			SAT_value = false;
			itr++;// ignore the sign from the SAT_variable
			while (token[itr] != '\0')
				SAT_variable += token[itr++];
		}

		set_SATvariable_assignment(stoi(SAT_variable), SAT_value);
	}
}

void SAT_vertex::generate_output_retargeting_vector()
{
	//To find the scan-in data for the primary scan input of a network in the i-th CSU operation, the network’s graph is traversed along the active scan path of frame i − 1. The content of visited scan segments is acquired from the i-th time frame of the satisfying assignment.
	//so ASP can be concluded from the sel() value of time frame (TF).
	//while constent of ASP can be infered from the state() value of time frame (TF+1).

	unsigned int TF = 0;
	unsigned int sat_assignment;
	unsigned int NW_size = NW_stateElements.size() * 3;//(*3) assuming the network has V nodes = Vs + Va + Vp = (scan_segments=NW_stateElements.size()) + (auxilary_nodes=NW_stateElements.size()) + (primary_nodes=NW_stateElements.size()). 

	//reserve space for the "initial" Time Frame
	SAT_output.emplace_back(); //this constructor is used with any two dimentional vector, where this emplace_back() is used with the outer vector to initialize and reserve the internal vector capacity.
	SAT_output.back().reserve(NW_size); //this is the max that all NW state elements and NW shift registers are part of the ASP.

	if (no_timeFrames > 0)
	{
		for (size_t index = 0, e = NW_SAT_variables.size(); index < e; index++)
		{
			if (NW_SAT_variables[index].timeFrame == TF)
			{
				if ((NW_SAT_variables[index].type == 2) && (NW_SAT_variables[index].SAT_assignment == true))	//false to select the ineternal_control_signal variables/ (sel) variables, (SAT_assignment == true) means this scan segment is active and selected through this time frame. Similar to [if(NW_SAT_variables[i].is_Active)] in SCT_to_SAT model.
				{
					if (TF < no_timeFrames)
					{
						if (is_SCB(NW_SAT_variables[index].id))
						{
							sat_assignment = get_SATvariable_assignment(NW_SAT_variables[index].id, TF + 1, true); //(true) b/c I want the content/state of the scan segment from the next TF of the satisfying assignmnet. 
							SAT_output.back().emplace_back(NW_SAT_variables[index].id, sat_assignment);
						}
						else //sat_assignment "could not" be exist if it is not a state element variable like (SI, SO, AUX) where they only have "select" SAT_variables and no associated "state" variables.
							SAT_output.back().emplace_back(NW_SAT_variables[index].id, -1);  //(-1) means (UNKOWN) state, where the shift_register's "state" value is assumed to be unkown we only predict its "select" state if it is Active or not through each TF.
					}
					else //if(TF  == no_timeFrames). for the last TF, we need to consider only the (select) variable, which would be used in generating the last ASP, and hence to be considered while computing the number of cycles associated with each retargeting solution.
						SAT_output.back().emplace_back(NW_SAT_variables[index].id, -1);
				}
			}
			else
			{
				//Now we could move to the next TF:
				if ((TF + 1) == no_timeFrames)	//this is a stoping condition where we don't need the "select" state or the ASP for the timeFrames which come after the entered no of time frames.
					break;

				TF++;
				index--; //to "Recheck" on that SAT_variable (NW_SAT_variables[i].timeFrame) after updating the time frame slot associated with the next CSU output vector.

				//reserve space for the the "next" Time Frame
				SAT_output.emplace_back();
				SAT_output.back().reserve(NW_size);
			}
		}
	}
	else //in case (TF==0), generate the output from the initial_configuration input, where the (target_reg) is *already* Active and accessable with no need for retargetig vectors to put it on the ASP.
	{
		for (size_t index = 0, e = NW_SAT_variables.size(); index < e; index++)
		{
			if ((NW_SAT_variables[index].type == 2) && (NW_SAT_variables[index].SAT_assignment == true))	//false to select the ineternal_control_signal variables/ (sel) variables, (SAT_assignment == true) means this scan segment is active and selected through this time frame. Similar to [if(NW_SAT_variables[i].is_Active)] in SCT_to_SAT model.
			{
				if (is_SCB(NW_SAT_variables[index].id))
					SAT_output.back().emplace_back(NW_SAT_variables[index].id, initial_configuration);

				else //sat_assignment "could not" be exist if it is not a state element variable like (SI, SO, AUX) where they have only "select" SAT_variables and no "state" variables.
					SAT_output.back().emplace_back(NW_SAT_variables[index].id, -1);  //(-1) means (UNKOWN) state, where the shift_register's "state" value is assumed to be unkown we only predict its "select" state if it is Active or not through each TF.
			}
		}
	}
}

void SAT_vertex::print_file(_SAT_Type option, const string& file_name, const string& file_opening_option)
{
	FILE *file;
	string output_text = "";

	if ((file = fopen(file_name.c_str(), file_opening_option.c_str())) != NULL) //"a" for append or "w" for write.
	{
		switch (option)
		{
		case SAT_clauses:
		{
			/*
			The first non-comment line must be of the form:
			p cnf NUMBER_OF_VARIABLES NUMBER_OF_CLAUSES
			Each of the non-comment lines afterwards defines a clause.
			Each of these lines is a space-separated list of variables.
			a positive value means that corresponding variable (so 4 means x4),
			and a negative value means the negation of that variable (so -5 means -x5).
			Each line must end in a space and the number 0.
			EX:
			p cnf 5 3
			1 -5 4 0
			*/

			for (size_t i = 0, e = NW_SAT_clauses.size(); i < e; i++)
				output_text += NW_SAT_clauses[i] + "\n";

			break;
		}
		case SAT_retargeting_vectors:
		{
			output_text = "The Retaregeting output vectors for (" + NW_TDRs.back().reg_id + ") using (" + to_string(no_timeFrames) + " CSUs) is: \n";
			//output_text += satisfiable_string + "\n";

			for (unsigned int i = 0, e1 = SAT_output.size(); i < e1; i++)
			{
				output_text += "ASP for TF(" + to_string(i) + ") is: ";
				for (unsigned int j = 0, e2 = SAT_output[i].size(); j < e2; j++)
				{
					if ((SAT_output[i][j].clause.find("AUX") == std::string::npos) && (SAT_output[i][j].clause.find("TDI") == std::string::npos) && (SAT_output[i][j].clause.find("TDO") == std::string::npos)) //Where we want to ignore AUX nodes, primary nodes (TDI,TDO) from being printed
					{
						output_text += SAT_output[i][j].clause + " = ";
						if (SAT_output[i][j].state != -1)
							output_text += to_string(SAT_output[i][j].state) + ", ";
						else
							output_text += "X, ";  //"X" for unknown.
					}
				}
				output_text += "\n";
			}

			output_text += "Number of Clock Cycles = " + to_string(NW_TDRs.back().solver_returns.back().AccessTime) + "\n";
			output_text += "/////////////////////////////////////////////////////////////////////////////\n";
			break;
		}
		}
		fprintf(file, "%s", output_text.c_str());
		fclose(file);
	}
	else printf("%s \n", "Unable to open file");
}

void SAT_vertex::print_vectors_size_capacity_comparison()
{
	FILE *file;
	string file_name = path + "NW_vectors_sizes.txt";

	if ((file = fopen(file_name.c_str(), "a")) != NULL)	// use "a" for append, "w" to overwrite, previous content will be deleted. https://stackoverflow.com/questions/2393345/how-to-append-text-to-a-text-file-in-c
	{
		fprintf(file, "\n//////////////////////////FOR Structural_SAT//////////////////////////\n");
		fprintf(file, "SAT_predicates: Size= %lu, \t Capacity= %lu\n", NW_SAT_predicates.size(), Expected_no_predicates); //where size_t and .size() are of type: long unsigned int (https://stackoverflow.com/questions/4033018/how-to-print-an-unsigned-long-int-with-printf-in-c/4033039)
		fprintf(file, "SAT_clauses: Size= %lu, \t Capacity= %lu\n", NW_SAT_clauses.size(), NW_SAT_clauses.capacity());
		fprintf(file, "SAT_variables: Size= %lu, \t Capacity= %lu\n", NW_SAT_variables.size(), Expected_no_SATvariables);
		fprintf(file, "////////////////////////////////////////////////////////////////////////////////////\n");

		fclose(file);
	}
	else printf("%s \n", "Unable to open pdl file");
}

void SAT_vertex::print_NWstatistics(bool target_statistics, unsigned int index)
{
	//statistics for specific "target_reg"
	if ((target_statistics) && (NW_TDRs[index].solver_returns.size() > 0)) //(NW_TDRs[index].solver_returns.size() > 0) check if there exist a retargeting solution or not!!
	{
		printf("\n//////////////////////////////////////////////////////////////////");
		printf("\n*******For %s: *******\n", NW_TDRs[index].reg_id.c_str());
		printf("\nFor SAT_problem size : #variables = %lu, #clauses = %lu", NW_TDRs[index].n_SAT_variables, NW_TDRs[index].n_SAT_clauses);
		printf("\nNumber of Conflicts = %f", get_avg('C'));
		printf("\nInstrument Access Time = %f", get_avg('A'));
		printf("\nRetargeting took %f s", get_avg('E'));

		printf("\n\n//////////////////////////////////////////////////////////////////\n");
	}

	//statistics for the "whole" NW	
	else if (NW_TDRs[index].solver_returns.size() > 0)
	{
		printf("\n//////////////////////////////////////////////////////////////////");

		printf("\nNumber of TDR's = %d", NW_TDRs.size());
		printf("\nFor SAT_problem size : \n\t#vars_Avg/#clauses_Avg = %f/%f, #vars_Max/#clauses_Max = %f/%f", get_avg('V'), get_avg('L'), get_max('V'), get_max('L'));
		printf("\nFor Conflicts NW parameter:\n\tAvg= %f, Max= %f", get_avg('C'), get_max('C'));
		printf("\nFor Access time(CC) NW parameter:\n\tAvg= %f, Max= %f", get_avg('A'), get_max('A'));
		printf("\nFor Execution time(sec) NW parameter:\n\tAvg= %f, Max= %f", get_avg('E'), get_max('E'));

		printf("\n//////////////////////////////////////////////////////////////////\n");
	}
}

double SAT_vertex::get_avg(char x) //A->access time, C->no of Conflicts, E->execution time
{
	double sum_avg = 0;
	double sum_TDR = 0;

	switch (x) {
	case 'A':
	{
		unsigned int i, j, e1, e2, n_retargeted_TDRs = 0;	//n_retargeted_TDRs: represent the number of NW_TDRs that could be retargetted using the assigned number of CSUs
		for (i = 0, e1 = NW_TDRs.size(); i < e1; i++)
		{
			if ((e2 = NW_TDRs[i].solver_returns.size()) > 0)
			{
				n_retargeted_TDRs++;
				for (j = 0; j < e2; j++)
					sum_avg += NW_TDRs[i].solver_returns[j].AccessTime;

				sum_avg /= e2; //took the avg per TDR w.r.t. the different possible retargeting solutions.
				sum_TDR += sum_avg;
				sum_avg = 0; //to be used in the next iteration
			}
		}
		return (n_retargeted_TDRs != 0) ? (sum_TDR / n_retargeted_TDRs) : 0; //in case the assigned number of CSUs is not sufficient for the retargetting of any NW_TDR, at then (n_retargeted_TDRs=0)!!
		break;
	}
	case 'C':
	{
		unsigned int i, j, e1, e2, n_retargeted_TDRs = 0;	//n_retargeted_TDRs: represent the number of NW_TDRs that could be retargetted using the assigned number of CSUs
		for (i = 0, e1 = NW_TDRs.size(); i < e1; i++)
		{
			if ((e2 = NW_TDRs[i].solver_returns.size()) > 0)
			{
				n_retargeted_TDRs++;
				for (j = 0; j < e2; j++)
					sum_avg += NW_TDRs[i].solver_returns[j].n_conflicts;

				sum_avg /= e2; //took the avg per TDR w.r.t. the different possible retargeting solutions.
				sum_TDR += sum_avg;
				sum_avg = 0; //to be used in the next iteration
			}
		}
		return (n_retargeted_TDRs != 0) ? (sum_TDR / n_retargeted_TDRs) : 0;
		break;
	}
	case 'E':
	{
		unsigned int i, j, e1, e2, n_retargeted_TDRs = 0;	//n_retargeted_TDRs: represent the number of NW_TDRs that could be retargetted using the assigned number of CSUs
		for (i = 0, e1 = NW_TDRs.size(); i < e1; i++)
		{
			if ((e2 = NW_TDRs[i].solver_returns.size()) > 0)
			{
				n_retargeted_TDRs++;
				for (j = 0; j < e2; j++)
					sum_avg += NW_TDRs[i].solver_returns[j].execution_time;
				
				sum_avg /= e2; //took the avg per TDR w.r.t. the different possible retargeting solutions.
				sum_TDR += sum_avg;
				sum_avg = 0; //to be used in the next iteration
			}
		}
		return (n_retargeted_TDRs != 0) ? (sum_TDR / n_retargeted_TDRs) : 0;
		break;
	}
	case 'V':
	{
		unsigned int i, e;
		for (i = 0, e = NW_TDRs.size(); i < e; i++)
		{
			sum_TDR += NW_TDRs[i].n_SAT_variables;
		}
		return (sum_TDR / e); //e can't be zero; it mus be at least one target_reg!!
		break;
	}
	case 'L':
	{
		unsigned int i, e;
		for (i = 0, e = NW_TDRs.size(); i < e; i++)
		{
			sum_TDR += NW_TDRs[i].n_SAT_clauses;
		}
		return (sum_TDR / e);
		break;
	}
	default: std::printf("Passed parameter isn't valid!!"); // no error
		return -1;
		break;
	}
}

double SAT_vertex::get_max(char x)
{
	switch (x) {
	case 'A':
	{
		double max = NW_TDRs[0].solver_returns[0].AccessTime;
		for (size_t i = 0, e1 = NW_TDRs.size(); i < e1; i++)//(i,j) start from (0).
		{
			for (size_t j = 0, e2 = NW_TDRs[i].solver_returns.size(); j < e2; j++)
			{
				if (max < NW_TDRs[i].solver_returns[j].AccessTime)
					max = NW_TDRs[i].solver_returns[j].AccessTime;
			}
		}
		return max;
		break;
	}
	case 'C':
	{
		double max = NW_TDRs[0].solver_returns[0].n_conflicts;
		for (size_t i = 0, e1 = NW_TDRs.size(); i < e1; i++)//(i,j) start from (0).
		{
			for (size_t j = 0, e2 = NW_TDRs[i].solver_returns.size(); j < e2; j++)
			{
				if (max < NW_TDRs[i].solver_returns[j].n_conflicts)
					max = NW_TDRs[i].solver_returns[j].n_conflicts;
			}
		}
		return max;
		break;
	}
	case 'E':
	{
		double max = NW_TDRs[0].solver_returns[0].execution_time;
		for (size_t i = 0, e1 = NW_TDRs.size(); i < e1; i++) //(i,j) start from (0).
		{
			for (size_t j = 0, e2 = NW_TDRs[i].solver_returns.size(); j < e2; j++)
			{
				if (max < NW_TDRs[i].solver_returns[j].execution_time)
					max = NW_TDRs[i].solver_returns[j].execution_time;
			}
		}
		return max;
		break;
	}
	case 'V':
	{
		double max = NW_TDRs[0].n_SAT_variables;
		for (size_t i = 1, e = NW_TDRs.size(); i < e; i++)
		{
			if (max < NW_TDRs[i].n_SAT_variables)
				max = NW_TDRs[i].n_SAT_variables;
		}
		return max;
		break;
	}
	case 'L':
	{
		double max = NW_TDRs[0].n_SAT_clauses;
		for (size_t i = 1, e = NW_TDRs.size(); i < e; i++)
		{
			if (max < NW_TDRs[i].n_SAT_clauses)
				max = NW_TDRs[i].n_SAT_clauses;
		}
		return max;
		break;
	}
	default: printf("Passed parameter isn't valid!!"); // no error
		return -1;
		break;
	}
}