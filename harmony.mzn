enum Voice = {Tenor, Lead, Baritone, Bass};

set of int: MidiNote = 0..127;
set of int: Duration = index_set(melody);

Voice: sings_melody;

array[Voice] of set of MidiNote: range = [58..70, 50..65, 47..65, 41..58];

array[int] of set of MidiNote: possible_chords;
set of int: Chord = index_set(possible_chords);
array[int] of MidiNote: melody;

array[Duration] of var Chord: progression;
array[Voice, Duration] of var MidiNote: harmony;
array[Voice, Duration] of var 0..11: raw_note = array2d(Voice, Duration, [harmony[v,d] mod 12 | v in Voice, d in Duration]);

constraint forall(v in Voice, d in Duration) (harmony[v,d] in range[v]);
constraint harmony[sings_melody,..] = melody;

constraint forall(d in Duration) (
  { raw_note[v, d] | v in Voice } = possible_chords[progression[d]]
);

constraint forall(d in Duration) (
  melody[d] in possible_chords[progression[d]]
);

constraint forall(v1, v2 in Voice, d in Duration where d != max(Duration)) (
  (abs(raw_note[v1,d] - raw_note[v2,d]) = 7) -> (abs(harmony[v1,d+1] - harmony[v2,d+1]) != 7)
);