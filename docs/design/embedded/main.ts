import { append, fromArray, length } from "./list.ts";
import { binarySearch } from "./search.ts";
import { get, replicate, zip } from "./vec.ts";
import { length_append } from "./list.proof.ts";

const xs = fromArray([1, 2, 3]);
console.log("length(append) =", length(append(xs, fromArray([4, 5]))));
console.log("binarySearch =", binarySearch([1, 3, 5, 7, 9], 7));
console.log("zip =", JSON.stringify(zip(replicate(2, "a"), [true, false])));
console.log("get =", get([10, 20, 30], 2));

// Run as plain TS, a theorem is a property test on the inputs you give it.
length_append(xs, fromArray([4, 5]));
console.log("length_append holds for these inputs");

// TypeScript accepts this (Vec is just an array to tsc). ProofScript rejects it:
// the lengths differ, so there is no single n with Vec<A, n> and Vec<B, n>.
console.log("bad zip =", JSON.stringify(zip([1, 2, 3], ["x"])));
