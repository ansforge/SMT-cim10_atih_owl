package fr.gouv.esante.smt.utils;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.Charset;
import java.util.Properties;

public class MetadataUtil {

  
    public static String getProperties(final String propertieName, String... onto ) {

      String versionString = null;

      // to load application's properties, we use this class
      final Properties mainProperties = new Properties();

      FileInputStream file;
      String metafile;
      // the base folder is ./, the root of the main.properties file
      final String path = "./Metadata.properties";
      final String ICDpath = "./ICD11_Metadata.properties";
      final String CISPpath = "./CISP2_Metadata.properties";
      final String CladiMedpath = "./CLADIMED_Metadata.properties";
      if(null != onto && onto.length > 0) {
        switch(onto[0]) {
          case "ICD11":
            metafile = ICDpath;
            break;
          case "CISP2":
            metafile = CISPpath;
            break; 
          case "CLADIMED":
            metafile = CladiMedpath;
            break;
          default:
            metafile = path;
        }
      }else {
        metafile = path;
      }

      // load the file handle for main.properties
      try {
        file = new FileInputStream(metafile);
        // load all the properties from this file
        mainProperties.load(new InputStreamReader(file, Charset.forName("UTF-8")));
        // retrieve the property we are intrested, the app.version
        versionString = mainProperties.getProperty(propertieName, "");
        // we have loaded the properties, so close the file handle
        file.close();
      } catch (final FileNotFoundException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      } catch (final IOException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }



      return versionString;
    }

}
