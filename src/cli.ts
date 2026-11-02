import { compileProofScriptModule, verifyProofScriptModule } from "./verify.js";

function usage(): never {
  throw new Error(
    "Usage: proofscript verify <path-to-proofscript-module>\n       proofscript compile <path-to-proofscript-module>",
  );
}

async function main(): Promise<void> {
  const [, , command, sourcePath] = process.argv;

  if (sourcePath === undefined) {
    usage();
  }

  if (command === "compile") {
    const emittedJavaScriptPath = await compileProofScriptModule(sourcePath);
    process.stdout.write(`${JSON.stringify({ emittedJavaScriptPath }, null, 2)}\n`);
    return;
  }

  if (command === "verify") {
    const result = await verifyProofScriptModule(sourcePath);
    process.stdout.write(`${JSON.stringify(result, null, 2)}\n`);
    return;
  }

  usage();
}

main().catch((error: unknown) => {
  const message = error instanceof Error ? error.stack ?? error.message : String(error);
  process.stderr.write(`${message}\n`);
  process.exitCode = 1;
});
