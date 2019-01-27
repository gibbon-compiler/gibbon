pipeline {
  // This is designed to run on Cutter @ IU
  // agent {
  //   label 'slurm'
  // }

  triggers {
      // Try to create a webhook:
      pollSCM('')
  }

  environment {
      // COARSE_DOCKER='1'
      // COARSE_NIX='1'
  }
    
  stages {
    stage('Build') {
      steps {
        // sh 'srun -N1 -t 1:00:00 --exclusive "./.jenkins_script.sh"'
        sh './.jenkins_script.sh'
      }
    }
  }
}
