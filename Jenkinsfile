pipeline {
  // This is designed to run on Cutter @ IU
  agent {
    label 'linux-ubuntu-1604'
  }

  triggers {
      // Try to create a webhook:
      pollSCM('')
  }

  stages {
    stage('Build') {
      steps {
        // sh 'srun -N1 -t 1:00:00 "./.jenkins_script.sh"'
        sh './.jenkins_script.sh'
      }
    }
  }
}
