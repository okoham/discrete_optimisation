% this version passes solution submissions A1 and A2.


% scheduling suitors
enum SUITOR;
SUITOR: LiuBei; % which suitor is LiuBei
int: n; % number of meetings
set of int: MEETING = 1..n;
array[MEETING] of SUITOR: suitor;

enum ROOM = { Red, Gold, Blue };
array[SUITOR,ROOM] of int: mintime;
array[SUITOR,ROOM] of int: maxtime;
constraint forall(s in SUITOR, r in ROOM)
                 (assert(mintime[s,r] >= 1 /\ maxtime[s,r] >= mintime[s,r],
                  "error in mintime/maxtime at [\(s),\(r)]\n"));

array[ROOM,ROOM] of int: move;
constraint forall(r in ROOM)(assert(move[r,r] = 0,"move[\(r),\(r)] != 0\n"));

int: ndays; % number of days
set of int: DAY = 1..ndays;
int: earliest; % time for earliest meeting start
int: latest;  % time for end of latest meeting

int: lessontime; % time for kung fu lesson;
int: minsep;     % minimum time between consecutive kung fu lessons

array[ROOM] of int: usedstart;  % time others use each room each day
array[ROOM] of int: useddur;    % durations of others use

enum STAGE = {A,B,C};
STAGE: stage;

set of int: TIME = 0..24*ndays;

array[MEETING] of var TIME: start;
array[MEETING] of var TIME: dur;    % duration in false schedule
array[MEETING] of var ROOM: room;
set of int: KUNGFU = 1..n;
array[KUNGFU] of var int: kungfu;  % start time for each lesson
% unused kungfu lessons have start times after 24*ndays

% temporary workaround for kungfu
constraint stage in {A, B} /\ forall(k in KUNGFU)(kungfu[k] = 1 + 24*ndays);

% meeting durations are not fixed! they have a min/max depending on suitor and room.
constraint forall(i in MEETING)
                 (dur[i] >= mintime[suitor[i], room[i]] /\
                  dur[i] <= maxtime[suitor[i], room[i]]);

% no - the unary resource is Sun. We can't have parallel meetings. 
% but there are other resources using the rooms at fixed times. how to deal with that?
include "disjunctive.mzn";
constraint disjunctive(start, dur);

% time of day constraints
% TODO: nochmal prüfen ob das ende bei 0 oder 24 Uhr passt
% FIXME: meeting end time at 24h. 
constraint forall(i in MEETING)
                 (let {
                    var 0..23: tstart = start[i] mod 24; 
                    var int: tend = tstart + dur[i];  
                  } in 
                 tstart >= earliest /\ tend <= latest);
                  
% belegte Räume: usedstart, useddur (im 24 h format)
constraint forall(i in MEETING, r in ROOM where room[i] = r)
                 (let {
                    var earliest..latest: tstart = start[i] mod 24; 
                    var int: tend = tstart + dur[i];  
%                     var DAY: dstart = 1 + start[i] div 24; 
%                     var DAY: dend = 1 + (start[i] + dur[i]) div 24;   
                  } in 
                  (tend <= usedstart[r] \/ 
                   tstart >= usedstart[r] + useddur[r]));

% Liu Bei has to make a schedule for Sun Shangxiang which respects the time limits 
% with and without the kung fu lessons.


% Solution
% the objective value which is 100 for each kung fu lesson scheduled in the given 
% ndays plus the number of hours of meetings scheduled for Liu Bei
var int: obj = sum(i in MEETING where suitor[i] = LiuBei)(dur[i]);
solve maximize obj;

array[TIME] of var 0..n: X;
constraint forall(i in MEETING, t in TIME)
                 (start[i] <= t /\ start[i] + dur[i] > t <-> X[t] = i);  


output ["start = \(start);\n"] ++
       ["dur = \(dur);\n"] ++
       ["room = \(room);\n"] ++
       ["kungfu = \(kungfu);\n"] ++
       %["suitor = \(suitor);\n"] ++
       ["obj = \(obj);\n"]  ++
       
       ["\n"] ++
       ["  t D  H  i\n"] ++
       [if true then % t mod 24 in earliest-1..latest then
          show_int(3, t) ++ 
          show_int(2, 1 + t div 24) ++ 
          show_int(3, t mod 24) ++ "-" ++ show_int(2, 1 + t mod 24) ++
          if fix(X[t] > 0) then show_int(3, X[t]) else "   " endif ++
          if fix(X[t] > 0) then " " ++ show(suitor[X[t]]) else "  " endif ++
          if fix(X[t] > 0) then " " ++ show(room[X[t]]) else "    " endif ++
          "\n"
        else "" endif
        | t in TIME] ++
        
       [];
