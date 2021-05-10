% This passes problems B1 and B2

int: length; % height of lake
set of int: LENGTH = 0..length-1;
int: width; % width of lake
set of int: WIDTH = 0..width-1;

int: ntypes;  % number of types of ship
set of int: TYPE = 1..ntypes;
array[TYPE] of int: number;         % number of each type of ship
array[TYPE] of set of SHAPE: config; % configs for each type of ship

int: nshapes; % number of shapes
set of int: SHAPE = 1..nshapes;
set of int: SHAPE0 = 0..nshapes;
array[SHAPE] of set of ROFF: shape;

int: nroff; % number of rectangle offsets
set of int: ROFF = 1..nroff;
array[ROFF,1..4] of int: rectoff; % x offset, y offset, width, height

int: total_ships = sum(number);
set of int: SHIP = 1..total_ships;
array[SHIP] of var LENGTH:  x;
array[SHIP] of var WIDTH:   y;
array[SHIP] of var SHAPE0:  k;

array[LENGTH] of WIDTH: mist; % mist starts at this width, goes downward
array[WIDTH] of int: arrow;  % number of arrows that arrive at this height
array[TYPE] of int: price;
int: budget;
enum STAGE = {A,B,C,D,E,F};
STAGE: stage;

/*
length  ... is the length of the river in which to set boats,
width   ... is the width of the river, 
ntypes  ... is the number of different kinds of ships available, 
number  ... is an array mapping ship types to the number of ships of that type available, 
nroff   ... is the number of rectangle offset quadruples used to define ships, 
rectoff ... is a 2d array, each row is a rectangle offset (xoffset, yoffset, length, width).
            -> corresponds to d in lecture slides
nshapes ... is the number of different shapes (sets of rectangle offset quadruples),
shape   ... is a mapping from shape to set of rectangle offset quadruples, 
config  ... is a mapping from each type of ship to its set of possible shapes, 
mist    ... is array mappping length positions to where the mist begins on the river, 
arrows  ... is an array mapping width positions to how many 1000’s of arrows are
            likely to fall at that distance from Cao Cao’s camp, 
price   ... is an array mapping ship type to price to bribe, 
budget  ... is an integer giving available money for bribes, 
stage   ... is a enumerated type variable giving the stage in {A, B, C, D, E, F}.
*/

% type of each ship
array[TYPE] of int: psum = [ sum(i in 1..t-1)(number[i]) | t in TYPE ];
array[SHIP] of TYPE: shipshape = [ max(t in TYPE)(t*(s > psum[t])) | s in SHIP ];

% useful variables
% array[SHIP] of 1..length: sizex = [rectoff[i,3] | i in ROFF, j in 1..number[i]];
% array[SHIP] of 1..width:  sizey = [rectoff[i,4] | i in ROFF, j in 1..number[i]];

% DATA TRANSLATION
% extract the offsets and sizes
array[ROFF,1..2] of int: rsize = array2d(ROFF, 1..2, [rectoff[i,j] | i in ROFF, j in 3..4]);
array[ROFF,1..2] of int: roff  = array2d(ROFF, 1..2, [rectoff[i,j] | i in ROFF, j in 1..2]);

% pack the x and y coordinates
array[SHIP,1..2] of var 0..max(length, width): coord;
constraint forall(i in SHIP)(coord[i,1] = x[i] /\ coord[i,2] = y[i]);

% Squares fit in the rectangle
% constraint forall(s in SHIP)(x[s] + sizex[s] <= length);
% constraint forall(s in SHIP)(y[s] + sizey[s] <= width);

% nonoverlap
% include "diffn.mzn";
% constraint diffn(x, y, sizex, sizey);

% redundant constraint
% include "cumulative.mzn";
% constraint cumulative(x, sizex, sizey, width);
% constraint cumulative(y, sizey, sizex, length);


% set up the "kind" constraints
% array[SHIP] of var int: kind;     % kind=shipshape
% array[SHIP] of set of int: shapeind;   % shapeind == config?
% constraint forall(i in SHIP)(kind[i] in shapeind[i]);

include "geost.mzn";
constraint geost_bb(2,
                    rsize,
                    roff,
                    shape,
                    coord,
                    shipshape,
                    [0, 0],
                    [length, width]);


% symmetry breaking
include "lex_less.mzn";
include "lex_lesseq.mzn";
% constraint lex_lesseq(x, y);
constraint forall(s1, s2 in SHIP where s1 < s2)
                 (shipshape[s1] = shipshape[s2] -> (x[s1] <= x[s2]) /\ (y[s1] <= y[s2]));


% counts
%include "global_cardinality.mzn";
%constraint global_cardinality(k, [i | i in ROFF], number);

% objective
int: maxarrows = length * sum(arrow);
var 0..maxarrows: tarrows;
% var 0..maxarrows: tarrows = sum(s in SHIP)
%                       (sizex[s] * sum(j in 0..sizey[s]-1)(arrow[y[s] + j]));
% solve maximize tarrows;
solve satisfy;

% output             
output ["x = \(x);\n" ++ 
        "y = \(y);\n" ++ 
        "k = \(k);\n" ++ 
        "tarrows = \(tarrows);\n" ++
        
%         "psum = \(psum);\n" ++
%         "shipshape = \(shipshape);\n" ++
%         "sizex = \(sizex);\n" ++
%         "sizey = \(sizey);\n" ++
        
        ""
       ]