% 1.2 Input and Output - io.mzn

% Build a MiniZinc model io.mzn that takes a data file defining integer parameter n and outputs its
% value.
% Test it using different values of d as the value for n, which it should print out. In the IDE,
% running the model should pop up a box asking you to input the value for n. Using the command
% line you can enter the value d for parameter n as follows:
% minizinc io.mzn -D"n = d;"

int: n;
output ["\(n)\n"];
% alternatively: output [show(n)];