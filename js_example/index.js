import init, * as wasm from "../pkg/creator_compiler.js";

await init({})

const json_arch = await (await fetch("../tests/architecture.json")).text()

const arch = wasm.ArchitectureJS.from_json(json_arch);
console.log(arch.toString())
window["arch"] = arch

const src = document.getElementById("src");
const out = document.getElementById("result");

document.getElementById("compile_btn").onclick = function() {
  try {
    const compiled = arch.compile(src.value);
    console.log(compiled)
    // copy instruction data out of the wasm memory
    const instructions = compiled.instructions.map(x => ({
      address: x.address,
      labels: x.labels,
      loaded: x.loaded,
      binary: x.binary,
      user: x.user
    }));
    const data = compiled.data
    console.log(instructions)
    console.log(data)
    window["instructions"] = instructions
    window["data"] = data
    out.innerHTML = `Code compiled successfully\n${compiled.toString()}`
  } catch (e) {
    out.innerHTML = e;
  }
}
