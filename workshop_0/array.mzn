% 1.5 Arrays - array.mzn

% Define a MiniZinc model array.mzn which takes an integer parameter n defining the length of an
% array of numbers x taking values from 0 to 9. Constrain the array so the sum of the numbers in
% the array is equal to the product of the numbers in the array. Output the resulting array.

% Test it using the IDE set to print out all solutions as described for x110.mzn. Alternatively test
% your model from the command line using

% minizinc array.mzn -a

% which should print out all the solutions for x.

% Add a constraint to ensure that the numbers in the array are non-decreasing, i.e. 
% x[1] ≤ x[2] ≤ · · · ≤ x[n]. 
% This should reduce the number of similar solutions. This is an example of symmetry
% breaking which will be very useful.

% How big a number can you solve with your model? Why do you think this happens?

int: n;
array[1..n] of var 0..9: x;
constraint sum(x) = product(x);
constraint forall(i in 1..n-1)(x[i] <= x[i+1]);

solve satisfy;

output [show(x) ++ "\n"];