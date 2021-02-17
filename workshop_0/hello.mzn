% 1.1 Hello World - hello.mzn

% Build a MiniZinc model hello.mzn that outputs the result “Hello World”!
% Test it from the IDE or from the command line using
% minizinc hello.mzn

% in the solution video they say that at least one solve item is required; 
% however, it works without!
% solve satisfy;
output [ "Hello World\n" ];