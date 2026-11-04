import { by, decide, omega, prove, simp, type nat, type Proof } from "proofscript";

export function greet(name: string): string {
  return "hi " + name;
}

export function greet_length(name: string): Proof {
  return prove(greet(name).length === 3 + name.length, by(simp(greet), omega));
}

export function greet_starts(name: string): Proof {
  return prove(greet(name).startsWith("hi"), by(simp(greet)));
}

// JavaScript semantics: an emoji outside the Basic Multilingual Plane is two UTF-16 code units.
export function emoji_is_two_units(): Proof {
  return prove("😀".length === 2, decide);
}

export function firstCode(s: string, i: nat): nat {
  return i < s.length ? s.charCodeAt(i) : 0;
}
