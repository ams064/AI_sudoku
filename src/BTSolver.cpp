#include"BTSolver.hpp"

using namespace std;

// =====================================================================
// Constructors
// =====================================================================

BTSolver::BTSolver ( SudokuBoard input, Trail* _trail,  string val_sh, string var_sh, string cc )
: sudokuGrid( input.get_p(), input.get_q(), input.get_board() ), network( input )
{
	valHeuristics = val_sh;
	varHeuristics = var_sh; 
	cChecks =  cc;

	trail = _trail;
}

// =====================================================================
// Consistency Checks
// =====================================================================

// Basic consistency check, no propagation done
bool BTSolver::assignmentsCheck ( void )
{
	for ( Constraint c : network.getConstraints() )
		if ( ! c.isConsistent() )
			return false;

	return true;
}

// =================================================================
// Arc Consistency
// =================================================================
bool BTSolver::arcConsistency ( void )
{
    vector<Variable*> toAssign;
    vector<Constraint*> RMC = network.getModifiedConstraints();
    for (int i = 0; i < RMC.size(); ++i)
    {
        vector<Variable*> LV = RMC[i]->vars;
        for (int j = 0; j < LV.size(); ++j)
        {
            if(LV[j]->isAssigned())
            {
                vector<Variable*> Neighbors = network.getNeighborsOfVariable(LV[j]);
                int assignedValue = LV[j]->getAssignment();
                for (int k = 0; k < Neighbors.size(); ++k)
                {
                    Domain D = Neighbors[k]->getDomain();
                    if(D.contains(assignedValue))
                    {
                        if (D.size() == 1)
                            return false;
                        if (D.size() == 2)
                            toAssign.push_back(Neighbors[k]);
                        trail->push(Neighbors[k]);
                        Neighbors[k]->removeValueFromDomain(assignedValue);
                    }
                }
            }
        }
    }
    if (!toAssign.empty())
    {
        for (int i = 0; i < toAssign.size(); ++i)
        {
            Domain D = toAssign[i]->getDomain();
            vector<int> assign = D.getValues();
            trail->push(toAssign[i]);
            toAssign[i]->assignValue(assign[0]);
        }
        return arcConsistency();
    }
    return network.isConsistent();
}

/**
 * Part 1 TODO: Implement the Forward Checking Heuristic
 *
 * This function will do both Constraint Propagation and check
 * the consistency of the network
 *
 * (1) If a variable is assigned then eliminate that value from
 *     the square's neighbors.
 *
 * Note: remember to trail.push variables before you change their domain
 * Return: a pair of a map and a bool. The map contains the pointers to all MODIFIED variables, mapped to their MODIFIED domain. 
 * 		   The bool is true if assignment is consistent, false otherwise.
 */
pair<map<Variable*,Domain>,bool> BTSolver::forwardChecking ( void )
{
	map<Variable*, Domain> m;
	vector<Constraint*> RMC(network.getModifiedConstraints());
	for(int i = 0; i < RMC.size(); i++) {

	    vector<Variable*> LV(RMC[i]->vars);

	    for(int j = 0; j < LV.size(); j++) {

		if(LV[j]->isAssigned()) {
		    vector<Variable*> Neighbors(network.getNeighborsOfVariable(LV[j]));
		    int assigned_value = LV[j]->getAssignment();

		    for(int k = 0 ; k < Neighbors.size(); k++) {

			Domain d = Neighbors[k]->getDomain();
			if(d.contains(assigned_value)) {
			    if(d.size() == 1) {
				return {m,false};
			    } else {
				trail->push(Neighbors[k]);
				Neighbors[k]->removeValueFromDomain(assigned_value);
				if(m.find(Neighbors[k]) != m.end()) m.erase(Neighbors[k]);
				m.insert({Neighbors[k],Neighbors[k]->getDomain()});
			    }
			}
		    }
	     	}
	    }
	}		
	return {m,true};
}

/**
 * Part 2 TODO: Implement both of Norvig's Heuristics
 *
 * This function will do both Constraint Propagation and check
 * the consistency of the network
 *
 * (1) If a variable is assigned then eliminate that value from
 *     the square's neighbors.
 *
 * (2) If a constraint has only one possible place for a value
 *     then put the value there.
 *
 * Note: remember to trail.push variables before you change their domain
 * Return: a pair of a map and a bool. The map contains the pointers to all variables that were assigned during 
 *         the whole NorvigCheck propagation, and mapped to the values that they were assigned. 
 *         The bool is true if assignment is consistent, false otherwise.
 */
pair<map<Variable*,int>,bool> BTSolver::norvigCheck ( void )
{
        // 1) Removing values from domain.-> forwardchecking.
        map<Variable*, int> m;
        vector<Constraint*> RMC(network.getModifiedConstraints());
        for(int i = 0; i < RMC.size(); i++) {

            vector<Variable*> LV = RMC[i]->vars;

            for(int j = 0; j < LV.size(); j++) {

                if(LV[j]->isAssigned()) {
                    vector<Variable*> Neighbors(network.getNeighborsOfVariable(LV[j]));
                    int assigned_value = LV[j]->getAssignment();

                    for(int k = 0 ; k < Neighbors.size(); k++) {

                        Domain d = Neighbors[k]->getDomain();
                        if(d.contains(assigned_value)) {
                            if(d.size() == 1) {
                                return {m,false};
                            } else {
                                trail->push(Neighbors[k]);
                                Neighbors[k]->removeValueFromDomain(assigned_value);
                                //if(m.find(Neighbors[k]) != m.end()) m.erase(Neighbors[k]);
                                //m.insert({Neighbors[k],Neighbors[k]->getDomain()});
                            }
                        }
                    }
                }
            }
        }

                vector<Constraint*> C(network.getModifiedConstraints());
                for (int i = 0; i < C.size(); i++) {
                        std::unordered_map<int,vector<Variable*>> counter;
                        vector<Variable*> LV(C[i]->vars);
                        for(int j = 0 ; j < LV.size(); j++) {
                                if(!LV[j]->isAssigned()) {
                                vector<int> domain_values(LV[j]->getDomain().getValues());
                                        for(auto p : domain_values) {
                                                counter[p].push_back(LV[j]);
                                        }
                                }
                        }

                        for(auto const& p : counter) {
                                if(p.second.size() == 1) {
                                        Variable* v = p.second[0];
                                        trail->push(v);
                                        v->assignValue(p.first);
                                        m.insert({v,p.first});
                                }
                        }
                }
        return {m,network.isConsistent()};
}

/**
 * Optional TODO: Implement your own advanced Constraint Propagation
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
bool BTSolver::getTournCC ( void )
{
	return norvigCheck().second;
}

// =====================================================================
// Variable Selectors
// =====================================================================

// Basic variable selector, returns first unassigned variable
Variable* BTSolver::getfirstUnassignedVariable ( void )
{
	for ( Variable* v : network.getVariables() )
		if ( !(v->isAssigned()) )
			return v;

	// Everything is assigned
	return nullptr;
}

/**
 * Part 1 TODO: Implement the Minimum Remaining Value Heuristic
 *
 * Return: The unassigned variable with the smallest domain
 */
Variable* BTSolver::getMRV ( void )
{
        Variable* min_domain_var = nullptr;
        for (Variable* v : network.getVariables()) {
            if(!v->isAssigned()) {
                if (!min_domain_var) min_domain_var = v;
                else if (v->getDomain().size() < min_domain_var->getDomain().size())
                    min_domain_var = v;
            }
        }
       return min_domain_var;
}


/**
 * Part 2 TODO: Implement the Minimum Remaining Value Heuristic
 *                with Degree Heuristic as a Tie Breaker
 *
 * Return: The unassigned variable with the smallest domain and affecting the most unassigned neighbors.
 * 		   If there are multiple variables that have the same smallest domain with the same number 
 * 		   of unassigned neighbors, add them to the vector of Variables.
 *         If there is only one variable, return the vector of size 1 containing that variable.
 */
vector<Variable*> BTSolver::MRVwithTieBreaker ( void )
{
        Variable* min_domain_var(getMRV());
        vector<Variable*> tie_breakers;

        if(!min_domain_var) {
            tie_breakers.push_back(min_domain_var);
            return tie_breakers;
        }

        for (Variable* v : network.getVariables()) {
            if (!v->isAssigned()) {
                if (v->getDomain().size() == min_domain_var->getDomain().size())
                    tie_breakers.push_back(v);
            }
        }

	// Temp vector which holds varaibles and the number of neighbors (unassigned) the varibales is affecting.
	vector<pair<Variable*,int>> temp;
	int min_sum = -1;
	for(int i = 0; i < tie_breakers.size(); i++) {
		vector<Variable*> Neighbors(network.getNeighborsOfVariable(tie_breakers[i]));
		int sum = 0;
		for(int j = 0 ; j < Neighbors.size(); j++) {
		    if(!Neighbors[j]->isAssigned()) {
			sum++;
		    }
		}
		temp.push_back({tie_breakers[i],sum});
		min_sum = max(min_sum,sum);
	}

	vector<Variable*> retVal;

	for(int i = 0 ; i < temp.size(); i++) {
	    if(temp[i].second == min_sum)
		retVal.push_back(temp[i].first);
	}

	return retVal;
}

/**
 * Optional TODO: Implement your own advanced Variable Heuristic
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
Variable* BTSolver::getTournVar ( void )
{
	return getMRV();
}

// =====================================================================
// Value Selectors
// =====================================================================

// Default Value Ordering
vector<int> BTSolver::getValuesInOrder ( Variable* v )
{
	vector<int> values = v->getDomain().getValues();
	sort( values.begin(), values.end() );
	return values;
}

/**
 * Part 1 TODO: Implement the Least Constraining Value Heuristic
 *
 * The Least constraining value is the one that will knock the least
 * values out of it's neighbors domain.
 *
 * Return: A list of v's domain sorted by the LCV heuristic
 *         The LCV is first and the MCV is last
 */
vector<int> BTSolver::getValuesLCVOrder ( Variable* v )
{
    vector<Variable*> neighbors(network.getNeighborsOfVariable(v));
    vector<int> domain_vals(v->getDomain().getValues());
    int sum = 0;
    vector<pair<int,int>> temp;
    vector<int> lcv_order;
    bool valid_value = true;
    for (int i = 0; i < domain_vals.size(); i++){
        sum = 0;
        valid_value = true;
            for (int j = 0; j < neighbors.size(); j++) {
				if (neighbors[j]->getDomain().contains(domain_vals[i])) {
				if (neighbors[j]->getDomain().size() == 1) valid_value = false;
				else sum += neighbors[j]->getDomain().size() - 1;
			}
			else
				sum += neighbors[j]->getDomain().size();
			}
        if(valid_value)
            temp.push_back({domain_vals[i],sum});
    }

    sort(temp.begin(), temp.end(),[](const pair<int,int>& a, const pair<int,int>& b){
        if(a.second < b.second) return false;
        if(a.second == b.second) return a.first < b.first;
        return true;
    });

    for(auto p : temp) {
        lcv_order.push_back(p.first);
    }
    return lcv_order;
}

/**
 * Optional TODO: Implement your own advanced Value Heuristic
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
vector<int> BTSolver::getTournVal ( Variable* v )
{
	return getValuesLCVOrder(v);
}

// =====================================================================
// Engine Functions
// =====================================================================

int BTSolver::solve ( float time_left)
{
	if (time_left <= 60.0)
		return -1;
	double elapsed_time = 0.0;
    clock_t begin_clock = clock();

	if ( hasSolution )
		return 0;

	// Variable Selection
	Variable* v = selectNextVariable();

	if ( v == nullptr )
	{
		for ( Variable* var : network.getVariables() )
		{
			// If all variables haven't been assigned
			if ( ! ( var->isAssigned() ) )
			{
				return 0;
			}
		}

		// Success
		hasSolution = true;
		return 0;
	}

	// Attempt to assign a value
	for ( int i : getNextValues( v ) )
	{
		// Store place in trail and push variable's state on trail
		trail->placeTrailMarker();
		trail->push( v );

		// Assign the value
		v->assignValue( i );

		// Propagate constraints, check consistency, recurse
		if ( checkConsistency() ) {
			clock_t end_clock = clock();
			elapsed_time += (float)(end_clock - begin_clock)/ CLOCKS_PER_SEC;
			double new_start_time = time_left - elapsed_time;
			int check_status = solve(new_start_time);
			if(check_status == -1) {
			    return -1;
			}
			
		}

		// If this assignment succeeded, return
		if ( hasSolution )
			return 0;

		// Otherwise backtrack
		trail->undo();
	}
	return 0;
}

bool BTSolver::checkConsistency ( void )
{
	if ( cChecks == "forwardChecking" )
		return forwardChecking().second;

	if ( cChecks == "norvigCheck" )
		return norvigCheck().second;

	if ( cChecks == "tournCC" )
		return getTournCC();

	return assignmentsCheck();
}

Variable* BTSolver::selectNextVariable ( void )
{
	if ( varHeuristics == "MinimumRemainingValue" )
		return getMRV();

	if ( varHeuristics == "MRVwithTieBreaker" )
		return MRVwithTieBreaker()[0];

	if ( varHeuristics == "tournVar" )
		return getTournVar();

	return getfirstUnassignedVariable();
}

vector<int> BTSolver::getNextValues ( Variable* v )
{
	if ( valHeuristics == "LeastConstrainingValue" )
		return getValuesLCVOrder( v );

	if ( valHeuristics == "tournVal" )
		return getTournVal( v );

	return getValuesInOrder( v );
}

bool BTSolver::haveSolution ( void )
{
	return hasSolution;
}

SudokuBoard BTSolver::getSolution ( void )
{
	return network.toSudokuBoard ( sudokuGrid.get_p(), sudokuGrid.get_q() );
}

ConstraintNetwork BTSolver::getNetwork ( void )
{
	return network;
}
