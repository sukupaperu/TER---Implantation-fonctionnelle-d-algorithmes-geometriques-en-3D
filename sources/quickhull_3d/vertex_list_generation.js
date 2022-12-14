"use strict";

const GLOBAL_V_LIST = [];

const print_GLOBAL_V_LIST_constructor = () => {
    let q = "GLOBAL_V_LIST.push("; GLOBAL_V_LIST.forEach((x) => { q += "vec3(" + x.x + ',' + x.y + ',' + x.z + ")" + ','; }); q += ");"; console.log(q);
};

function export_global_v_list() {
    const globalVListToStr = () => {
        let str = "";
        GLOBAL_V_LIST.forEach(
            (v) => str += v.x + " " + v.y + " " + v.z + "\n"
        );
        return str;
    };
    const data_str = globalVListToStr();
    const data = new Blob([data_str], { type: "application/txt" });
    const download_button_element = document.createElement("a");
    download_button_element.setAttribute("href", window.URL.createObjectURL(data));
    download_button_element.setAttribute("download", "VertexList.txt");
    download_button_element.click();
}

function export_quick_result(convex_hull) {
    const convexHullToStr = () => {
        let str = "";
        convex_hull.he_list.forEach(
            (he) => str += he.vertex + "\n"
        );
        return str;
    };
    const data_str = convexHullToStr();
    const data = new Blob([data_str], { type: "application/txt" });
    const download_button_element = document.createElement("a");
    download_button_element.setAttribute("href", window.URL.createObjectURL(data));
    download_button_element.setAttribute("download", "Facelist.txt");
    download_button_element.click();
}

// ------------- Génération de points aléatoires -------------
for (let i = 0; i < 100; i++) {
    GLOBAL_V_LIST.push(
        multiply3_1(
            normalize3(
                minus3_1(vec3(Math.random(), Math.random(), Math.random()), .5)
            ),
            Math.cbrt(Math.random())// * 0 + 1
            //Math.random() ** 10
        )
        // multiply3_1(
        //     minus3_1(vec3(Math.random(), Math.random(), Math.random()), .5),
        //     Math.random() * .25)
    );
}