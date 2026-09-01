#!/usr/bin/env node

import assert from "node:assert/strict";
import { pathToFileURL } from "node:url";

const modulePath = process.argv[2];
if (!modulePath) throw new Error("usage: test-computation-bundle.mjs <bundle.mjs>");
const factory = (await import(pathToFileURL(modulePath))).default;
const instance = await factory();
instance._proof_script_init();
const encoder = new TextEncoder();
const decoder = new TextDecoder();

function invoke(entry, input) {
  const entryBytes = encoder.encode(entry);
  const inputBytes = encoder.encode(JSON.stringify(input));
  const entryPtr = instance._proof_script_alloc(entryBytes.length);
  const inputPtr = instance._proof_script_alloc(inputBytes.length);
  instance.HEAPU8.set(entryBytes, entryPtr);
  instance.HEAPU8.set(inputBytes, inputPtr);
  let capacity = 256;
  let outputPtr = instance._proof_script_alloc(capacity);
  let length = instance._proof_script_invoke(
    entryPtr, entryBytes.length, inputPtr, inputBytes.length, outputPtr, capacity,
  );
  if (length > capacity) {
    instance._proof_script_free(outputPtr);
    capacity = length;
    outputPtr = instance._proof_script_alloc(capacity);
    length = instance._proof_script_invoke(
      entryPtr, entryBytes.length, inputPtr, inputBytes.length, outputPtr, capacity,
    );
  }
  const result = JSON.parse(decoder.decode(instance.HEAPU8.slice(outputPtr, outputPtr + length)));
  instance._proof_script_free(entryPtr);
  instance._proof_script_free(inputPtr);
  instance._proof_script_free(outputPtr);
  return result;
}

assert.deepEqual(invoke("chooseOffset", true), { ok: true, value: 128 });
assert.deepEqual(invoke("doubleValue", { value: 21 }), { ok: true, value: { doubled: 42 } });
assert.equal(invoke("doubleValue", { value: 101 }).error.code, "computation-error");
assert.equal(invoke("missing", {}).error.code, "unknown-entry");

console.log(JSON.stringify({ entries: 2, cases: 4, status: "ok" }));
