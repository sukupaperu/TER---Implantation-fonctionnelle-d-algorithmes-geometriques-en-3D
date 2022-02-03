"use strict";

const vs = `#version 300 es

layout(location = 0) in vec3 v_in;

out vec3 v_coords;
out vec3 t_coords;

//uniform float u_time;
uniform float u_point_size;
uniform vec2 u_resolution;
uniform vec2 u_mouse;

#define M_PI   3.1415926
#define M_2_PI 6.2831853
#define M_PI_2 1.5707963

mat4 project(float n, float f, float e, float a) {
    float fl = f - n;
    return mat4(e, vec4(0.), e/a, vec4(0.), (f + n)/-fl, -1., vec2(0.), -(2.*f*n)/fl, 0.);
}

mat4 translate(vec3 p)
{
    return mat4(1., vec4(0.), 1., vec4(0.), 1., 0., p, 1.);
}

mat4 rotateXZ(float a)
{
    float c = cos(a), s = sin(a);
    return mat4(c, 0., s, vec2(0.), 1., vec2(0.), -s, 0., c, vec4(0.), 1.);
}

mat4 rotateYZ(float a)
{
    float c = cos(a), s = sin(a);
    return mat4(
        1., 0., 0., 0.,
        0., c, s, 0.,
        0., -s, c, 0.,
        0., 0., 0., 1.);
}

void main()
{
    vec4 p = vec4(v_in, 1.);

    mat4 rot1 = rotateXZ(-u_mouse.x/u_resolution.x*6.28);
    mat4 rot2 = rotateYZ(-u_mouse.y/u_resolution.y*6.28*.1);
    mat4 rot = rot1*rot2;

    mat4 V = translate(vec3(0., 0., -1.75))*rot;
    mat4 P = project(.01, 10., 1./.5, 1.);

    vec4 pos_out = P*V*p;

    v_coords = vec3(rot*p);
    t_coords = pos_out.xyz;

    gl_PointSize = u_point_size*1.5;
    gl_Position = pos_out;
}`;

const fs = `#version 300 es
precision highp float;

layout(location = 0) out vec4 fragColor;

in vec3 v_coords;
in vec3 t_coords;

uniform vec3 u_color;

void main()
{
    vec2 st = v_coords.xy/.1;

    float shading = smoothstep(-.5, 1.5, -v_coords.z + .5);

    vec3 color = gl_FrontFacing
        ? u_color - .85*shading
        : vec3(.5) - .25*shading;

    fragColor = vec4(color, 1.);
    
}`;

class display
{
    gl;
    wgl;

    timeline_el;
    timeline_value;

    mouse = {
        state: 0,
        x_val: 0, x_init: 0, x_curr: 0,
        y_val: 0, y_init: 0, y_curr: 0
    };

    vbo_vertices;
    shader_prg;
    u_time;
    u_point_size;
    u_color;

    repere;

    vao_all_vertices = null;
    vao_convex_hull = null;
    vao_list = [];
    
    constructor(canvas_el, timeline_el)
    {
        this.wgl = new wgl(canvas_el);
        this.gl = this.wgl.get_gl();

        this.timeline_el = timeline_el;
        this.timeline_el.disabled = true;
        this.timeline_el.min = -1;
        this.timeline_el.max = 1;
        this.timeline_el.step = 1;
        this.timeline_el.value = this.timeline_value = -1;

        this.init_events();

        let gl = this.gl;
        this.shader_prg = this.wgl.init_shader_program(vs, fs);
        // this.u_time = gl.getUniformLocation(this.shader_prg, "u_time");
        this.u_point_size = gl.getUniformLocation(this.shader_prg, "u_point_size");
        this.u_color = gl.getUniformLocation(this.shader_prg, "u_color");
        this.u_resolution = gl.getUniformLocation(this.shader_prg, "u_resolution");
        this.u_mouse = gl.getUniformLocation(this.shader_prg, "u_mouse");
        
        this.repere = this.wgl.new_repere(.2);
    }

    init_events()
    {
        this.timeline_el.addEventListener("input", () => {
            this.timeline_value = parseInt(this.timeline_el.value);
            this.new_frame();
        });

        const event_mouse_x = (e) => e.clientX - e.target.offsetLeft;
        const event_mouse_y = (e) => e.clientY - e.target.offsetTop;
        this.gl.canvas.addEventListener("mousedown", (e) => {
            if(this.mouse.state === 0)
            {
                this.mouse.state = 1;
                this.mouse.x_init = this.mouse.x_curr = event_mouse_x(e);
                this.mouse.y_init = this.mouse.y_curr = event_mouse_y(e);
            }
        });
        const event_leave_up = (ev) => {
            if(this.mouse.state === 1 || this.mouse.state === 2)
            {
                this.mouse.state = 0;
                this.mouse.x_val += this.mouse.x_curr - this.mouse.x_init;
                this.mouse.x_init = this.mouse.x_curr = 0;
                this.mouse.y_val += this.mouse.y_curr - this.mouse.y_init;
                this.mouse.y_init = this.mouse.y_curr = 0;
            }
        };
        this.gl.canvas.addEventListener("mouseup", event_leave_up);
        this.gl.canvas.addEventListener("mouseleave", event_leave_up);
        this.gl.canvas.addEventListener("mousemove", (e) => {
            const px = e.clientX - e.target.offsetLeft;
            const py = e.clientY - e.target.offsetTop;
            if(this.mouse.state === 1)
                this.mouse.state = 2;
            else if(this.mouse.state === 2)
            {
                this.mouse.x_curr = event_mouse_x(e);
                this.mouse.y_curr = event_mouse_y(e);
                this.new_frame();
            }
        });
    }

    init_vertex_list(list)
    {
        let max_x = list.reduce((p,q) => p.x > q.x ? p : q).x;
        let min_x = list.reduce((p,q) => p.x < q.x ? p : q).x;
        let diff_x = max_x - min_x;
        let max_y = list.reduce((p,q) => p.y > q.y ? p : q).y;
        let min_y = list.reduce((p,q) => p.y < q.y ? p : q).y;
        let diff_y = max_y - min_y;
        let max_z = list.reduce((p,q) => p.z > q.z ? p : q).z;
        let min_z = list.reduce((p,q) => p.z < q.z ? p : q).z;
        let diff_z = max_z - min_z;

        let min_coord = Math.max(Math.max(min_x, min_y), min_z);
        let max_coord = Math.max(Math.max(max_x, max_y), max_z);
        let diff = max_coord - min_coord;
        diff_x = (diff_x/diff)*.5;
        diff_y = (diff_y/diff)*.5;
        diff_z = (diff_z/diff)*.5;

        const defined_or_zero = (x) => Number.isNaN(x) ? 0 : x;

        let gl = this.gl;
        let new_list = new Array(list.length*3);
        for(let i = 0; i < list.length; i++)
        {
            new_list[i*3] = defined_or_zero((list[i].x - min_x)/diff - diff_x);
            new_list[i*3 + 1] = defined_or_zero((list[i].y - min_y)/diff - diff_y);
            new_list[i*3 + 2] = defined_or_zero((list[i].z - min_z)/diff - diff_z);
        }

        this.vbo_vertices = this.wgl.init_vbo_position(new_list);
        this.vao_all_vertices = this.wgl.new_vao(new_ordered_int_list(list.length), this.vbo_vertices);

        this.vao_list = [];
    }

    push_result_indices(list)
    {
        this.vao_convex_hull = this.wgl.new_vao(list, this.vbo_vertices);
    }

    push_indices(list)
    {
        this.vao_list.push(this.wgl.new_vao(list, this.vbo_vertices));
    }

    push_he_l(he_l)
    {
        let list = [];
        he_for_each_faces(
            he_l,
            he_i =>
                he_for_each_vertices(
                    he_l,
                    he_i,
                    (x,y,z) => list.push(x,y,z)
                )
            )
        ;
        this.vao_list.push(this.wgl.new_vao(list, this.vbo_vertices));
    }

    set_ready()
    {
        this.timeline_el.max = this.vao_list.length + 1;
        this.timeline_el.disabled = false;
    }

    autoplay()
    {
        this.timeline_el.disabled = true;
        const autoplay_rec = (i) => {
            if(i <= parseInt(this.timeline_el.max))
            {
                window.setTimeout(() => {
                    this.timeline_el.value = this.timeline_value = i;
                    this.new_frame();
                    //this.wgl.capture_frame(1, frame" + "i);
                    autoplay_rec(i + 1);
                }, 100);
            }
            else
            {
                this.timeline_el.disabled = false;
            }
        }
        autoplay_rec(0);
    }

    new_frame()
    {
        let gl = this.gl;

        const loop = () =>
        {
            const time = performance.now()*.001;

            gl.viewport(0, 0, gl.canvas.width, gl.canvas.height);
            gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);

            gl.useProgram(this.shader_prg);
            //gl.uniform1f(this.u_time, time);
            gl.uniform2f(this.u_resolution, 
                gl.canvas.width,
                gl.canvas.height
            );
            gl.uniform2f(this.u_mouse, 
                (this.mouse.x_val + this.mouse.x_curr - this.mouse.x_init),
                (this.mouse.y_val + this.mouse.y_curr - this.mouse.y_init)
            );

            if(this.timeline_value - 1 < this.vao_list.length)
            {
                const rend_step = (i) =>
                {
                    if(i < 0) return;
                    const vao = this.vao_list[i];
                    vao.bind();
                    if(i === this.timeline_value)
                    {
                        gl.uniform3f(this.u_color, 1, 1, 1);
                        gl.uniform1f(this.u_point_size, 6);
                        gl.drawElements(gl.TRIANGLE, vao.nb_tri, gl.UNSIGNED_INT, 0);
                        gl.uniform3f(this.u_color, 1, 1, 0);
                    }
                    else gl.uniform3f(this.u_color, 1, 0, 0);
                    gl.drawElements(gl.TRIANGLES, vao.nb_tri, gl.UNSIGNED_INT, 0);
                };
                // rend_step(Math.min(this.timeline_value + 1, this.vao_list.length - 1));
                rend_step(Math.min(this.timeline_value, this.vao_list.length - 1));
            }
            else
            {
                this.vao_convex_hull.bind();
                gl.uniform3f(this.u_color, 1, 1, 1);
                gl.uniform1f(this.u_point_size, 5);
                gl.drawElements(gl.POINTS, this.vao_convex_hull.nb_tri, gl.UNSIGNED_INT, 0);
                gl.uniform3f(this.u_color, 0, 1, 0);
                gl.drawElements(gl.TRIANGLES, this.vao_convex_hull.nb_tri, gl.UNSIGNED_INT, 0);
            }

            gl.uniform3f(this.u_color, 1, 1, 1);
            gl.uniform1f(this.u_point_size, 2);
            this.vao_all_vertices.bind();
            gl.drawElements(gl.POINTS, this.vao_all_vertices.nb_tri, gl.UNSIGNED_INT, 0);

            this.repere.draw(this.u_color);

            gl.bindVertexArray(null);
            gl.useProgram(null);

            //window.requestAnimationFrame(loop);
        }
        window.requestAnimationFrame(loop)
    }

}