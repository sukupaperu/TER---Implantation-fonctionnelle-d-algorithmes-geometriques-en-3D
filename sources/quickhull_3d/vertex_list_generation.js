"use strict";

const GLOBAL_V_LIST = [];

const print_GLOBAL_V_LIST_constructor = () =>
{
    let q="GLOBAL_V_LIST.push(";GLOBAL_V_LIST.forEach((x)=>{q += "vec3("+x.x+','+x.y+','+x.z+")"+',';});q+=");";console.log(q);
};

function export_global_v_list_to_coq_file() {
    const print_to_coq_GLOBAL_V_LIST_constructor = () =>
    {
        let str = "Require Import _3d_trigo List.\nRequire Export List.\n\n";
        str += "Definition GLOBAL_V_LIST :=\n";
        GLOBAL_V_LIST.forEach(
            (v) => str += "(Vec3 (" + v.x + ") (" + v.y+") (" + v.z + "))\n\t:: "
        );
        str += "nil\n.";
        return str;
    };
    const coq_str = print_to_coq_GLOBAL_V_LIST_constructor();
    const data = new Blob([coq_str], {type: "application/text"});
    const download_button_element = document.createElement("a");
    download_button_element.setAttribute("href", window.URL.createObjectURL(data));
    download_button_element.setAttribute("download","global_v_list.v");
    download_button_element.click();
}

// ------------- Génération de points aléatoires -------------
for (let i = 0; i < 100; i++)
{
    GLOBAL_V_LIST.push(
        multiply3_1(
            normalize3(
                minus3_1(vec3(Math.random(), Math.random(), Math.random()), .5)
            ),
            Math.cbrt(Math.random())//*0 + 1
            //Math.random()**1000
        )
        //multiply3_1(
        //minus3_1(vec3(Math.random(), Math.random(), Math.random()), .5),
        //Math.random()**2)
    );
}