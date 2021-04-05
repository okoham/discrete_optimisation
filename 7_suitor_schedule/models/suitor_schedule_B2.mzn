% models for submission, time limit 60 s each: 
% A0, A3, B2, B4, C1, C3

% Idea 1: use a next construct, like in the channel example
% Idea 2: three workers (one for each room), each has a capacity 1, then use cumulative. 
%         can incorporate fixed tasks into that.

% multiple (unary) resources
% think of it as assigning tasks to workers. Each of the worker is a unary resource. They
% (notionally) work on all tasks but the ones they are not assigned are given a resource usage 
% of 0. The ones they do work on have a resource usage of 1. They have the capacity of working 
% on one task. This can be encoded with cumulative. Add the times of unavailability of each
% worker as tasks with fixed start time and duration and resource usage of 1. These tasks only 
% appear in the cumulative constraint for that worker.

% next works better than order/argsort

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

set of int: TIME = 0..24*ndays; % only start times, or also end times???
set of int: STIME = 0..24*ndays-1;

array[MEETING] of var STIME: start;
array[MEETING] of var TIME: dur;    % duration in false schedule
array[MEETING] of var ROOM: room;
set of int: KUNGFU = 1..n;
array[KUNGFU] of var int: kungfu;  % start time for each lesson
% unused kungfu lessons have start times after 24*ndays

% temporary workaround for kungfu
constraint stage in {A, B} /\ forall(k in KUNGFU)(kungfu[k] = 1 + 24*ndays);

% dummy meetings and next array 
% int: nR = card(ROOM);
% int: dummy = 0;
% set of int: MEETINGE = 0..n; % add dummy meeting
% array[MEETING] of var MEETINGE: next; % next meeting
% constraint alldifferent(next);

% order
array[1..n] of var MEETING: order = arg_sort(start);


% meeting durations are not fixed! they have a min/max depending on suitor and room.
constraint forall(m in MEETING)
                 (dur[m] >= mintime[suitor[m], room[m]] /\
                  dur[m] <= maxtime[suitor[m], room[m]]);

% no - the unary resource is Sun. We can't have parallel meetings. 
% but there are other resources using the rooms at fixed times. how to deal with that?

predicate nonoverlap(var int:s1, var int:d1,
                     var int:s2, var int:d2)=
          s1 + d1 <= s2 \/ s2 + d2 <= s1;

predicate freeroom(var TIME: begin, var int: duration, var ROOM: r) = 
  let {
    var int: sm = begin mod 24;
  } in nonoverlap(sm, duration, 0, earliest) /\
       nonoverlap(sm, duration, latest, 24-latest) /\
       nonoverlap(sm, duration, usedstart[r], useddur[r]);

% constraint forall(i in MEETING)(freeroom(start[i], dur[i], room[i]));

% incorrect (schedules a meeting at t=0)
% takes too long.
include "globals.mzn";
constraint forall(r in room)
                 (disjunctive(
                   [24*(d-1) + 0 | d in DAY] ++             % morning
                   [24*(d-1) + latest | d in DAY] ++        % evening
                   [24*(d-1) + usedstart[r] | d in DAY] ++  % used
                   [if room[i] = r then start[i] else <> endif | i in MEETING],

                   [earliest | d in DAY] ++ 
                   [24 - latest | d in DAY] ++ 
                   [useddur[r] | d in DAY] ++
                   dur
                 ));


% TODO: can we include this into the disjunctive?
% include "disjunctive.mzn";
% constraint disjunctive(start, dur);

predicate time_between(var TIME: s1, var int: d1, var TIME: s2, var int: gap) = 
  s1 + d1 + gap <= s2;  
  
% constraint forall(m in MEETING where next[m] != dummy)
%    (time_between(start[m], dur[m], start[next[m]], move[room[m], room[next[m]]]));
   
constraint stage in {B, C} -> forall(j in 1..n-1)
    (let {
        var MEETING: i1 = order[j];
        var MEETING: i2 = order[j+1]; 
    } in 
  time_between(start[i1], dur[i1], start[i2], move[room[i1], room[i2]]));


% Solution
% the objective value which is 100 for each kung fu lesson scheduled in the given 
% ndays plus the number of hours of meetings scheduled for Liu Bei
% range: n*max(maxtime) + n*100
% TODO for stage C: subtract kungfu time from liubei time
int: omin = count(SUITOR, LiuBei)*min(row(mintime, LiuBei));
int: omax = count(SUITOR, LiuBei)*max(row(maxtime, LiuBei)) + n*100;
var omin..omax: obj = sum(i in MEETING where suitor[i] = LiuBei)(dur[i]);
solve maximize obj;


% array[STIME] of var 0..n: X;
% constraint forall(i in MEETING, t in STIME)
%                  (start[i] <= t /\ start[i] + dur[i] > t <-> X[t] = i);  

output ["start = \(start);\n"] ++
       ["dur = \(dur);\n"] ++
       ["room = \(room);\n"] ++
       ["kungfu = \(kungfu);\n"] ++
       %["suitor = \(suitor);\n"] ++
       ["order = \(order);\n"] ++
%        ["next = \(next);\n"] ++
       ["obj = \(obj);\n"]  ++
       
%        ["\n"] ++
%        ["  t D     H  i SU  RM\n"] ++
%        [if true then % t mod 24 in earliest-1..latest then
%           show_int(3, t) ++ 
%           show_int(2, 1 + t div 24) ++ 
%           show_int(3, t mod 24) ++ "-" ++ show_int(2, 1 + t mod 24) ++
%           if fix(X[t] > 0) then show_int(3, X[t]) else "   " endif ++
%           if fix(X[t] > 0) then " " ++ show(suitor[X[t]]) else "  " endif ++
%           if fix(X[t] > 0) then " " ++ show(room[X[t]]) else "    " endif ++
%           "\n"
%         else "" endif
%         | t in STIME] ++
        
       [];
