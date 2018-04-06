let shalu_funct = fun (i:float) -> (3.0)*.i;;
let differential_shallu (delta_x) = (shalu_funct(float delta_x+.0.001) -. shalu_funct(float delta_x-.0.001))/.0.002;;
let pitzer_correlation p_initial t_initial p_final t_final omega pc tc = 