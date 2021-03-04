% Beauty Trap
% Create the most magnificient feast 
enum DISH;
enum TASTE = {spicy, sour, salty, sweet, umame, bland};
enum TEMP = {hot, cold, warm};
%int: ndish;
%set of int: DISH = 1..ndish;
%set of int: TASTE = 1..6;
%int: spicy = 1; int: sour = 2; int: salty = 3; int: sweet = 4; int: umame = 5; int: bland = 6;
%set of int: TEMP = 1..3;
%int: hot = 1; int: cold = 2; int: warm = 3;


array[DISH] of TASTE: taste;
array[DISH] of TEMP: temp;
array[DISH] of bool: heavy;
array[DISH] of int: value;

int: len; % length of banquet
set of int: COURSE = 1..len;

array[COURSE] of var DISH: dish;

% ------------------------
% first solution
% works, but takes 1:33 on data _2
% ------------------------

% each dish only served once
include "alldifferent.mzn";
constraint alldifferent(dish);
% don't serve two dishes of the same taste in a row
constraint forall(i in 1..len-1)(taste[dish[i]] != taste[dish[i+1]]);
% first dish salty, last dish sweet
constraint taste[dish[1]] = salty;
constraint taste[dish[len]] = sweet;
% after a spicy dish, serve bland or sweet
constraint forall(i in 1..len-1)
                 (taste[dish[i]] = spicy -> taste[dish[i+1]] = bland \/ taste[dish[i+1]] = sweet);
% after a sour dish, serve bland or umami
constraint forall(i in 1..len-1)
                 (taste[dish[i]] = sour -> taste[dish[i+1]] = bland \/ taste[dish[i+1]] = umame);
% no spicy or umame directly after sweet
constraint forall(i in 1..len-1)
                 (taste[dish[i]] = sweet -> (taste[dish[i+1]] != spicy) /\ (taste[dish[i+1]] != umame));
% between serving a hot dish and a later cold dish there must be a warm dish
% or, put differently, no cold dish after a hot one
constraint forall(i in 1..len-1)
                 (temp[dish[i]] = hot -> temp[dish[i+1]] != cold);
% no more than two heavy dishes in a row
constraint forall(i in 1..len-2)
                 (heavy[dish[i]] /\ heavy[dish[i+1]] -> not heavy[dish[i+2]]);

% objective: the magnificience of the meal
var int: obj = sum(d in dish)(value[d])
             + sum(i in 1..len-1)(taste[dish[i]] != taste[dish[i+1]])
             + sum(i in 1..len-1)(temp[dish[i]] != temp[dish[i+1]])
             + sum(i in 1..len-1)(heavy[dish[i]] != heavy[dish[i+1]]);

solve maximize obj;

output ["dish = " ++ show(dish) ++ ";\nobj = \(obj);\n" ];