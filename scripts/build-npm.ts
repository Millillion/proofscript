// Builds the npm package `proofscript` (in dist/npm/proofscript): the type surface
// (packages/proofscript), the kernel and the checker compiled to JavaScript, and the
// `proofscript` command. Node does not run TypeScript from node_modules, so the published
// package is JavaScript with declarations.
//
// Usage: node scripts/build-npm.ts   (then `npm pack dist/npm/proofscript`)

import { spawnSync } from "node:child_process";
import { chmodSync, copyFileSync, mkdirSync, readFileSync, readdirSync, rmSync, statSync, writeFileSync } from "node:fs";
import { dirname, join, relative } from "node:path";

const root = new URL("..", import.meta.url).pathname;
const out = join(root, "dist", "npm", "proofscript");
const version = (JSON.parse(readFileSync(join(root, "package.json"), "utf8")) as { version: string }).version;

rmSync(out, { recursive: true, force: true });
mkdirSync(out, { recursive: true });

const tsconfig = join(root, "dist", "npm", "tsconfig.build.json");
writeFileSync(
  tsconfig,
  JSON.stringify(
    {
      extends: "../../tsconfig.json",
      compilerOptions: {
        noEmit: false,
        declaration: true,
        rewriteRelativeImportExtensions: true,
        rootDir: "../../packages",
        outDir: "proofscript/lib",
        noUnusedLocals: false,
        noUnusedParameters: false,
      },
      include: ["../../packages/proofscript/src/**/*.ts", "../../packages/kernel/src/**/*.ts", "../../packages/checker/src/**/*.ts"],
      exclude: [],
    },
    null,
    2,
  ),
);
const tsc = spawnSync(process.execPath, [join(root, "node_modules", "typescript", "bin", "tsc"), "-p", tsconfig], { encoding: "utf8" });
if (tsc.status !== 0) throw new Error(`tsc failed:\n${tsc.stdout}${tsc.stderr}`);

// The checker imports the kernel as a workspace package; in the npm package it is a sibling.
function* files(dir: string): Generator<string> {
  for (const f of readdirSync(dir)) {
    const p = join(dir, f);
    if (statSync(p).isDirectory()) yield* files(p);
    else yield p;
  }
}
const kernelIndex = join(out, "lib", "kernel", "src", "index.js");
for (const f of files(join(out, "lib", "checker"))) {
  if (!f.endsWith(".js") && !f.endsWith(".d.ts")) continue;
  const rel = relative(dirname(f), kernelIndex).replace(/\\/g, "/");
  const text = readFileSync(f, "utf8").replaceAll('"@proofscript/kernel"', `"${rel.startsWith(".") ? rel : `./${rel}`}"`);
  writeFileSync(f, text);
}
copyFileSync(join(root, "packages", "checker", "src", "library.json"), join(out, "lib", "checker", "src", "library.json"));

mkdirSync(join(out, "bin"));
writeFileSync(
  join(out, "bin", "proofscript.mjs"),
  `#!/usr/bin/env node
// The \`proofscript\` command: runs the checker with the stack it needs (deep proof terms).
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";

const cli = fileURLToPath(new URL("../lib/checker/src/cli.js", import.meta.url));
const r = spawnSync(process.execPath, ["--stack-size=65500", "--max-old-space-size=4096", cli, ...process.argv.slice(2)], { stdio: "inherit" });
process.exitCode = r.status ?? 1;
`,
);
chmodSync(join(out, "bin", "proofscript.mjs"), 0o755);

const checkerPkg = JSON.parse(readFileSync(join(root, "packages", "checker", "package.json"), "utf8")) as { dependencies: Record<string, string> };
writeFileSync(
  join(out, "package.json"),
  `${JSON.stringify(
    {
      name: "proofscript",
      version,
      description: "TypeScript with dependent types and formal verification: theorems and proofs in TypeScript, checked by a Lean-compatible kernel",
      license: "MIT",
      type: "module",
      repository: { type: "git", url: "git+https://github.com/Millillion/proofscript.git" },
      engines: { node: ">=24" },
      exports: { ".": { types: "./lib/proofscript/src/index.d.ts", default: "./lib/proofscript/src/index.js" } },
      bin: { proofscript: "./bin/proofscript.mjs" },
      files: ["lib", "bin", "README.md", "LICENSE"],
      dependencies: { typescript6: checkerPkg.dependencies.typescript6 },
    },
    null,
    2,
  )}\n`,
);
copyFileSync(join(root, "LICENSE"), join(out, "LICENSE"));
copyFileSync(join(root, "README.md"), join(out, "README.md"));
console.log(`built ${relative(root, out)} (proofscript ${version})`);
