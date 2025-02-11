import init, * as wasm from "../pkg/web/creator_compiler.js";
import * as compiler from "./compiler.mjs";

await init({})

const json_arch = await (await fetch("../tests/architecture.json")).text()

const arch = compiler.load(wasm, json_arch)
console.log(arch.toString())
window["arch"] = arch

const src = document.getElementById("src");
const out = document.getElementById("result");

document.getElementById("compile_btn").onclick = function() {
  try {
    const compiled = compiler.compile(wasm, arch, src.value);
    window["instructions"] = compiled.instructions
    window["data"] = compiled.data
    console.log(compiled.instructions)
    console.log(compiled.data)
    out.innerHTML = compiled.msg;
  } catch (e) {
    out.innerHTML = e;
  }
}
