#!/usr/bin/env node

import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFile } from "node:fs/promises";
import { resolve } from "node:path";
import { pathToFileURL } from "node:url";

const root = process.cwd();
const pagePath = process.argv[2];
if (!pagePath) throw new Error("usage: test-finalized-computation.mjs <page.json>");
const page = JSON.parse(await readFile(resolve(root, pagePath), "utf8"));
const computations = page.components
  .map(component => component.data?.computation?.value)
  .filter(Boolean);
assert.ok(computations.length > 0);
assert.ok(computations.every(value => value.execution.status === "ready"));

async function verifiedResource(reference) {
  const descriptor = reference.$resource;
  const path = resolve(root, descriptor.path);
  const bytes = await readFile(path);
  assert.equal(createHash("sha256").update(bytes).digest("hex"), descriptor.hash);
  assert.equal(bytes.length, descriptor.byteSize);
  return { path, bytes };
}

const execution = computations[0].execution;
await verifiedResource(execution.manifest);
await verifiedResource(execution.wasm);
const moduleResource = await verifiedResource(execution.module);
const instance = await (await import(pathToFileURL(moduleResource.path))).default();
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
console.log(JSON.stringify({ resources: 3, entries: computations.length, status: "ok" }));
