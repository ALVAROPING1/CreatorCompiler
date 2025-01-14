const fs = require("fs");
const wasm = require('../pkg/nodejs/creator_compiler.js');
/**@type {import("./compiler.mjs")} compiler */
import("./compiler.mjs").then(compiler => {
    const json_arch = fs.readFileSync(__dirname + "/../tests/architecture.json", "utf8")

    const arch = compiler.load(wasm, json_arch)
    const src = fs.readFileSync(process.argv[2], "utf8")

    try {
        const compiled = compiler.compile(arch, src);
        console.log(compiled.msg);
        console.log(compiled.instructions);
        console.log(compiled.data);
    } catch (e) {
        console.error(e);
    }
});

