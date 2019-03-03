package edu.cqu.main;

import edu.cqu.core.FinishedListener;
import edu.cqu.core.ProgressChangedListener;
import edu.cqu.core.Solver;
import edu.cqu.result.Result;
import edu.cqu.utils.FileUtils;

import java.io.File;

/**
 * Created by dyc on 2019/3/1.
 */
public class Main {
    public static void main(String[] args){
        Solver solver = new Solver();

        // problems/am.xml PTISABB problems/RANDOM_ADCOP_8_8_density_0.25_13.xml result/
        String algoConfigurePath;
        String algoName ;
        String problemPath;
        String solutionPath;
        if (args.length != 4) {
            System.out.println("The parameter should be (algoConfigurePath: problem/am.xml,algoName: PTISABB,problemPath: problem/RANDOM_ADCOP_8_8_density_0.25_13.xml,solutionPath: result/)");
            return;
        }
        algoConfigurePath = args[0];
        algoName = args[1];
        problemPath = args[2];
        solutionPath = args[3];

        solver.solve(algoConfigurePath, algoName, problemPath, new FinishedListener() {
            @Override
            public void onFinished(Result result) {
                System.out.println("The optimal cost: " + result.getTotalCost());
                FileUtils.writeStringToFile(" " + result.getTotalCost(),solutionPath + "" + algoName +"/cost.txt");
            }
        }, false, false);

    }
}
