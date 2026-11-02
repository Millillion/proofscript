const BASE64_ALPHABET =
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

const unique = <T>(values: readonly T[]): T[] => {
  const seen = new Set<T>();
  const result: T[] = [];
  for (const value of values) {
    if (seen.has(value)) {
      continue;
    }
    seen.add(value);
    result.push(value);
  }
  return result;
};

export interface FiniteDomain {
  readonly name: string;
  readonly values: readonly unknown[];
}

const domains = new Map<string, FiniteDomain>([
  [
    "Byte",
    {
      name: "Byte",
      values: Array.from({ length: 256 }, (_, index) => index),
    },
  ],
  [
    "Sextet",
    {
      name: "Sextet",
      values: Array.from({ length: 64 }, (_, index) => index),
    },
  ],
  [
    "CodeUnit",
    {
      name: "CodeUnit",
      values: Array.from({ length: 65536 }, (_, index) => index),
    },
  ],
  [
    "CodeUnitString",
    {
      name: "CodeUnitString",
      values: Array.from({ length: 65536 }, (_, index) => String.fromCharCode(index)),
    },
  ],
  [
    "Base64Char",
    {
      name: "Base64Char",
      values: unique([...BASE64_ALPHABET, "-", "_"]),
    },
  ],
]);

export function getFiniteDomain(name: string): FiniteDomain {
  const domain = domains.get(name);
  if (domain === undefined) {
    throw new Error(`Unknown ProofScript finite domain: ${name}`);
  }
  return domain;
}

export function hasFiniteDomain(name: string): boolean {
  return domains.has(name);
}
