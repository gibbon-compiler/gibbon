pipeline {
  // This is designed to run on Cutter @ IU
  agent {
    label 'slurm'
  }

  triggers {
      // Try to create a webhook:
      pollSCM('')
  }

  stages {
    stage('Build') {
      steps {
        sh 'srun -N1 -t 1:00:00 --exclusive "./.jenkins_script.sh"'
        // sh './.jenkins_script.sh'
      }
    }
  }
}
