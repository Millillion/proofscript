import { append, fromArray, length } from "./list.ts";
import { binarySearch, isSorted } from "./search.ts";
import { get, replicate, zip } from "./vec.ts";
import { length_append } from "./list.ts";

const xs = fromArray([1, 2, 3]);
console.log("length(append) =", length(append(xs, fromArray([4, 5]))));

const sorted = [1, 3, 5, 7, 9];
// No cast needed: inside the `if`, ProofScript knows isSorted(sorted) holds.
if (isSorted(sorted)) console.log("binarySearch =", binarySearch(sorted, 7));

console.log("zip =", JSON.stringify(zip(replicate(2, "a"), [true, false])));
console.log("get =", get([10, 20, 30], 2));

// Run as plain TS, a theorem is a property test on the inputs you give it.
length_append(xs, fromArray([4, 5]));
console.log("length_append holds for these inputs");

// tsc accepts both calls below (to TS, Vec is an array and Lt<...> is unknown).
// ProofScript rejects both: the lengths differ, and 3 is not < 3.
console.log("bad zip =", JSON.stringify(zip([1, 2, 3], ["x"])));
console.log("bad get =", get([10, 20, 30], 3));
