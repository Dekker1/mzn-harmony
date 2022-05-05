include "globals.mzn";

enum Voice;

set of int: MidiNote = 0..127;
set of int: RawNote = 0..11;
set of int: Duration = index_set(melody);

% The melody singer
Voice: sings_melody;

% Vocal ranges (should be descending ranges)
array[Voice] of set of MidiNote: ranges;

% Valid chords
enum Chord;
array[Chord] of set of RawNote: possible_chords;
array[int] of MidiNote: melody;

% Chord progression of harmonisation
array[Duration] of var Chord: progression;

% Notes sung by each voice
array[Voice, Duration] of var MidiNote: harmony;
array[Voice, Duration] of var RawNote: raw_note = [(v, d): harmony[v, d] mod 12 | v in Voice, d in Duration];

% Melody singer is fixed
constraint harmony[sings_melody, ..] = melody;

% Notes within vocal ranges
constraint forall(v in Voice, d in Duration) (harmony[v, d] in ranges[v]);

% Notes at any given point form a chord in the progression
constraint forall(d in Duration) (
  let {
    var set of MidiNote: singing = { raw_note[v, d] | v in Voice };
  } in
    singing subset possible_chords[progression[d]] /\
    card(singing) >= 2 % Can't all sing the same note
);

% No consecutive perfect intervals
constraint forall(v1, v2 in Voice, d in Duration where d != max(Duration) /\ v1 < v2) (
  let {
    var int: current_interval = abs(raw_note[v1, d] - raw_note[v2, d]);
    var int: next_interval = abs(raw_note[v1, d + 1] - raw_note[v2, d + 1]);
    var bool: is_repeated = harmony[v1, d] = harmony[v1, d + 1] /\ harmony[v2, d] = harmony[v2, d + 1];
  } in current_interval in {0, 5, 7} -> next_interval != current_interval \/ is_repeated
);

% Total distance moved by voices
var int: distance = sum(v in Voice, d in Duration where d != max(Duration)) (abs(harmony[v, d] - harmony[v, d + 1]));

% 3 consecutive repeated notes
var int: repeats = count(v in Voice, d in Duration where d < enum_prev(max(Duration))) (
  harmony[v, d] = harmony[v, d + 1] /\ harmony[v, d] = harmony[v, d + 2]
);

% Voices out of order
var int: out_of_order = count(v in Voice, d in Duration where v != max(Voice)) (harmony[v, d] < harmony[enum_next(v), d]);

% Minimize penalties (TODO: weighting)
var int: objective :: output = distance + out_of_order + repeats;

solve minimize objective;
