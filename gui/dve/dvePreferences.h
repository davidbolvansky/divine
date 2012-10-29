/***************************************************************************
 *   Copyright (C) 2009 by Martin Moracek                                  *
 *   xmoracek@fi.muni.cz                                                   *
 *                                                                         *
 *   DiVinE is free software, distributed under GNU GPL and BSD licences.  *
 *   Detailed licence texts may be found in the COPYING file in the        *
 *   distribution tarball. The tool is a product of the ParaDiSe           *
 *   Laboratory, Faculty of Informatics of Masaryk University.             *
 *                                                                         *
 *   This distribution includes freely redistributable third-party code.   *
 *   Please refer to AUTHORS and COPYING included in the distribution for  *
 *   copyright and licensing details.                                      *
 ***************************************************************************/

#ifndef DVE_PREFERENCES_H_
#define DVE_PREFERENCES_H_

#include <QWidget>

class QTreeWidget;
class QTreeWidgetItem;
class QMenu;
class QAction;

namespace divine {
namespace gui {

/*!
 * This class implements the preferences page for DVE syntax highlighting.
 */
class DvePreferences : public QWidget {
  Q_OBJECT

  public:
    //! Contains highlighting information for one category.
    struct HighlightInfo {
      bool bold;                    //!< Use bold font.
      bool italic;                  //!< Use italic font.
      bool underline;               //!< Use underlined font.
      const char * foreground;      //!< Foreground color.
      const char * background;      //!< Background color.
    };
    
  public:
    DvePreferences(QWidget * parent=NULL);
    ~DvePreferences();

  public slots:
    void readSettings();
    void writeSettings();

  private:
    QTreeWidget * tree_;

    QTreeWidgetItem * target_;

    QMenu * menu_;
    QAction * resetForeAct_;
    QAction * resetBackAct_;

  private slots:
    void onItemDoubleClicked(QTreeWidgetItem * item, int column);
    void onItemChanged(QTreeWidgetItem * item, int column);
    void onCustomContextMenuRequested(const QPoint & pos);
    void onResetForeground();
    void onResetBackground();
};

extern const DvePreferences::HighlightInfo dveDefs[];

}
}

#endif
