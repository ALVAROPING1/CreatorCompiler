WEB_TARGET="web"
CLI_TARGET="nodejs"

function Info(){
    echo -e '\033[1;34m'"Build:\033[0m $*";
}

function Build() {
    wasm-pack build --target "$1" $2 --out-dir "pkg/$1"
}

function Move() {
    mv "pkg/$WEB_TARGET/$1" "pkg/$1"
    rm "pkg/$CLI_TARGET/$1"
}

function Cleanup() {
    Move .gitignore
    Move LICENSE
    Move README.md
}

function BuildFull() {
    Build $WEB_TARGET $1
    Build $CLI_TARGET $1
    Cleanup
}


function Help() {
    printf "Builds the compiler for usage in WebAssembly

Usage: \`./build.sh <command>\`

Commands available:

* release: build package with optimizations
* debug: build package without optimizations
* help/-h: show this message
"
}


case "$1" in
    '')
        BuildFull
        ;;
    'release')
        BuildFull
        ;;
    'debug')
        BuildFull --dev
        ;;
    'help')
        Help
        ;;
    '-h')
        Help
        ;;
    *)
        Info 'Unknown argument, see `./build.sh help`'
        ;;
esac
