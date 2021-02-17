% 1.4 Simple Optimization - xopt.mzn

% Build a MiniZinc model xopt.mzn with a decision variable x taking values from 0 to 10, with
% constraints to ensures that x is divisible by 4, which outputs the value of x that gives the minimum
% value of (x − 7)^2.

% Testing it in the IDE you should see that it prints out more than one solution. The last solution
% is the optimal, and the others are solutions found on the search to the optimal.
% Or test it on the command line using

% minizinc xopt.mzn

% which should print out just the optimal solution, or instead

% minizinc xopt.mzn -a

% which should print out all the solutions it found on the way to the optimal. Notice how the -a
% flag means different things for satisfaction problems (all solutions to the problem) and optimization
% problems (all solutions found on the way to the optimal). In the IDE the default behavior for
% optimization problems is to print out all solutions on the way to the optimal.

% Question: Suppose you cannot use the mod function, how would you alternatively model that x
% is divisible by 4?


var 0..10: x;
% solve minimize pow(x - 7, 2);
solve minimize (x - 7) ^ 2;

% model with mod function
constraint x mod 4 = 0;

% model without mod function. Choose a reasonable value for k
% var 1..3: k;
% constraint x = 4*k;


output ["\(x)\n"];